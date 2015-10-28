# This file is part of NIT ( http://www.nitlanguage.org ).
#
# Copyright 2015 Julien Pagès <julien.pages@lirmm.fr>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Single-Static Assignment algorithm from an AST
module ssa

import semantize
import astbuilder

# Represent a sequence of the program
# A basic block is composed of several instructions without a jump
class BasicBlock
	# The instructions in the basic block (a sequence without a jump)
	var instructions = new List[AExpr]

	# Direct successors
	var successors = new Array[BasicBlock]

	# Direct predecessors
	var predecessors = new Array[BasicBlock]

	# Parts of AST that contain a read to a variable
	var read_sites = new Array[AVarFormExpr]

	# Parts of AST that contain a variable access (read or write)
	var variables_sites = new Array[AExpr]

	# The environment is linked to each BasicBlock, it represents the latest versions of variables
	var environment = new HashMap[Variable, Array[AExpr]]

	# For each original variable, the last version
	var versions = new HashMap[Variable, Variable]

	# The iterated dominance frontier of this block
	# i.e. the set of blocks this block dominate directly or indirectly
	var dominance_frontier: Array[BasicBlock] = new Array[BasicBlock] is lazy

	# The list of BasicBlock which called `compute_environment` for this block,
	# used to handle circuits and recursions in computation of environments
	var callers_blocks = new Array[BasicBlock]

	# Compute the environment of the current block
	fun compute_environment(ssa: SSA)
	do
		if nb_treated == 5 then
			return
		end

		nb_treated += 1

		fill_environment(ssa)

		# Finally, launch the recursion in successors block
		for block in successors do
			block.callers_blocks.add(self)
			block.compute_environment(ssa)
		end
	end

	fun fill_environment(ssa: SSA)
	do
		# By default, clone a predecessor environment,
		# If there is no predecessor, this is the root_block and just initialize it
		if not predecessors.is_empty then
			environment = predecessors.first.clone_environment
		end

		var other_predecessors = new Array[BasicBlock]
		other_predecessors.add_all(predecessors)

		other_predecessors.remove_at(0)

		for other in other_predecessors do
			for key, value in other.environment do
				if not environment.has_key(key) then
					environment[key] = new Array[AExpr]
					environment[key].add_all(value)
				end
			end

			for key, value in other.versions do
				if versions.has_key(key) then
					# If the two versions differs, we need to create a PhiFunction
					if value != versions[key] then
						# Do not re-create a phi-function if there is already one for this variable
						var phi: nullable PhiFunction = lookup_phi(value.original_variable)

						if phi == null then
							# Place a phi-functions at the beginning of the block
							phi = new PhiFunction("phi", self)
							phi.block = self
							phi.original_variable = value.original_variable
							phi.declared_type = value.original_variable.declared_type
							phi.assignment_blocks.add(self)
							ssa.phi_functions.add(phi)
						end

						phi.add_dependences(other, value)
						phi.add_dependences(self, versions[key])

						print "Place a phi function for {value.original_variable} {phi}"

						versions[value.original_variable] = phi
					end
				else
					# Add this versions to the current environment if there is no version yet
					if not versions.has_key(key) then
						versions[key] = value
					end
				end
			end
		end

		# Handle the PhiFunction
		for variable in ssa.propdef.variables do
			if not environment.has_key(variable.original_variable) then
				environment[variable.original_variable] = new Array[AExpr]
			end

			# Search and merge the values of the variable
			for block in predecessors do
				if block.versions.has_key(variable.original_variable) and not versions.has_key(variable.original_variable) then
					versions[variable.original_variable] = block.versions[variable.original_variable]
				end

				if block.environment.has_key(variable.original_variable) then
					for expr in block.environment[variable.original_variable] do
						if not environment[variable.original_variable].has(expr) then
							environment[variable.original_variable].add(expr)
						end
					end
				end
			end
		end

		# Add all new variables to the environment
		for instruction in instructions do
			# Visit the instruction to collect variables sites
			variables_sites.remove_all
			instruction.visit_expression(ssa, self)

			for site in variables_sites do
				if site isa AVarExpr and site.variable == site.variable.original_variable then
					if not environment.has_key(site.variable.original_variable) then
						print "Problem in variables_sites with {site.variable.as(not null).original_variable} {instructions}"

						for key, value in environment do print "\tenv {key}-> {value}"
						abort
					else
						# Just copy the value inside the environment in the variable
						if versions.has_key(site.variable.original_variable) then
							site.variable = versions[site.variable.original_variable]
						else
							print "Problem with {site.variable.original_variable.to_s} in {self} {self.instructions}"
							print "{environment[site.variable.original_variable]}"

							for key,value in versions do
								print "\t{key} -> {value}"
							end
							abort
						end
						if not environment.has_key(site.variable.original_variable) then
							site.dump_tree
							print "erreur in environment {site.variable.original_variable}"
							for key, value in environment do print "\tenv {key}-> {value}"
							abort
						else
							site.variable.dep_exprs = environment[site.variable.original_variable].clone
						end
					end
				end
			end

			if instruction isa AVarAssignExpr then
				instruction.dump_tree
				# We need to create a new version of the variable
				var new_version = instruction.variable.original_variable.generate_version(instruction, ssa)

				# Replace by the new version in the AST-site
				print "{instruction.variable.as(not null)} {new_version} {new_version.original_variable}"
				instruction.variable = new_version
				versions[new_version.original_variable] = new_version

				environment[instruction.variable.original_variable].remove_all
				environment[instruction.variable.original_variable].add(instruction.n_value)

				print "After generation"
				for key, value in environment do print "\tenv {key}-> {value}"
				for key,value in versions do print "\tversions {key} -> {value}"
			end

			if instruction isa AVardeclExpr then
				# Add a new Variable to the environment
				environment[instruction.variable.as(not null)] = new Array[AExpr]

				# If there is an initial value
				if instruction.n_expr != null then
					environment[instruction.variable.as(not null).original_variable].add(instruction.n_expr.as(not null))
				end
				versions[instruction.variable.original_variable] = instruction.variable.as(not null)
			end
		end
	end

	# Return a new environment which is a copy of the current one
	fun clone_environment: HashMap[Variable, Array[AExpr]]
	do
		var clone = new HashMap[Variable, Array[AExpr]]
		var clone_versions = new HashMap[Variable, Variable]

		for variable, values in environment do
			clone[variable] = new Array[AExpr]
			clone[variable].add_all(values)
		end

		for key, value in versions do
			clone_versions[key] = value
		end

		return clone
	end

	# Self is the old block to link to the new,
	# The two blocks are not linked if the current ends with a `AReturnExpr` or `ABreakExpr`
	# i.e. self is the predecessor of `successor`
	# `successor` The successor block
	fun link(successor: BasicBlock)
	do
		successors.add(successor)
		successor.predecessors.add(self)
	end

	# Self is the old block to link to the new
	# i.e. self is the predecessor of `successor`
	# `successor` The successor block
	fun link_special(successor: BasicBlock)
	do
		# Link the two blocks even if the current block ends with a return or a break
		successors.add(successor)
		successor.predecessors.add(self)
	end

	# Compute recursively the dominance frontier of self block and its successors
	private fun compute_df
	do
		# Treat each block only one time
		df_computed = true

		for s in successors do
			dominance_frontier.add(s)

			if not s.df_computed then s.compute_df
		end
	end

	# Used to dump the BasicBlock to dot
	var treated_debug: Bool = false

	# If true, the iterated dominance frontier of this block has been computed
	var df_computed: Bool = false

	# Indicate if the variables renaming step has been made for this block
	var is_renaming: Bool = false

	# The variables that are accessed in this block
	var variables = new Array[Variable] is lazy

	# The PhiFunction this block contains at the beginning
	var phi_functions = new List[PhiFunction] is lazy

	# The number of times this block was treated by `compute_environment`
	var nb_treated = 0

	# Lookup in `phi_functions` a PhiFunction for the original variable (without renaming) `variable`
	# Return the looked Phi if found, else return null
	fun lookup_phi(variable: Variable): nullable PhiFunction
	do
		for phi in phi_functions do
			if phi.original_variable == variable then
				return phi
			end
		end

		return null
	end

	fun compute_environment_loop(ssa: SSA)
	do
		if nb_treated == 2 then
			return
		end

		nb_treated += 1

		fill_environment(ssa)

		# Finally, launch the recursion in successors block
		for block in successors do
			if block isa BodyLoopBlock then
				block.compute_environment_loop(ssa)
			else
				block.compute_environment(ssa)
			end
		end
	end
end

# A particular BasicBlock which is the test of a loop (for, while)
class TestLoopBlock
	super BasicBlock

	redef fun compute_environment(ssa: SSA)
	do
		compute_environment_loop(ssa)
	end
end

# A BasicBlock which is inside a loop
class BodyLoopBlock
	super BasicBlock
end

# Contain the currently analyzed propdef
class SSA
	# The currently analyzed APropdef
	var propdef: APropdef

	# The PhiFunction `current_propdef` contains
	var phi_functions = new Array[PhiFunction]

	# Recursively generate the basic blocks for this propdef
	fun generate_basic_blocks
	do
		propdef.generate_basic_blocks(self)
	end

	# Generate a BasicBlock structure for a if instruction
	# This method constructs several BasicBlock, one for each branch of the test and
	# returns the successor block of the if
	# *`old_block` The old_block which is terminated by the if
	# *`condition` The condition of the if
	# *`then_branch` The then branch
	# *`else_branch` The else branch
	# *`next_block` The following block to which the if must be linked
	fun generate_if(old_block: BasicBlock, condition: AExpr, then_branch: nullable AExpr, else_branch: nullable AExpr, next_block: BasicBlock)
	do
		# Create a single block for the test of the condition
		var block_test = new BasicBlock

		block_test.instructions.add(condition)

		old_block.link(block_test)

		# We start two blocks for the two branches
		var block_then = new BasicBlock
		var block_else = new BasicBlock

		block_test.link(block_then)
		block_test.link(block_else)

		# Launch the recursions in two branches,
		# and indicate to the branchs they need to be linked to the successor block
		var successor_block = new BasicBlock

		block_then.link(successor_block)
		block_else.link(successor_block)

		# Visit the test of the if
		condition.generate_basic_blocks(self, old_block, successor_block)

		successor_block.link(next_block)

		# Launch the recursion in two successors if they exist
		if then_branch != null then
			if not then_branch isa ABlockExpr then block_then.instructions.add(then_branch)
			then_branch.generate_basic_blocks(self, block_then, successor_block)
		end

		if else_branch != null then
			if not else_branch isa ABlockExpr then block_else.instructions.add(else_branch)
			else_branch.generate_basic_blocks(self, block_else, successor_block)
		end
	end

	# Generate a BasicBlock structure for a while instruction
	# This method constructs a block for the body of the loop and the appropriate structure
	# returns the successor block of the if
	# *`old_block` The old_block which is terminated by the while
	# *`condition` The condition of the loop
	# *`while_block` The block inside the while (if the test is true)
	# *`next_block` The following block to which the if must be linked
	fun generate_while(old_block: BasicBlock, condition: AExpr, while_block: nullable AExpr, next_block: BasicBlock)
	do
		# Create a single block for the test of the loop
		var block_test = new TestLoopBlock

		block_test.instructions.add(condition)

		old_block.link(block_test)

		# We start a block for the body
		var block_body = new BodyLoopBlock
		block_test.link(block_body)
		block_body.link(block_test)

		# The block after the while (if the test is false)
		var successor_block = new BasicBlock

		block_test.link(successor_block)

		# Visit the test of the if
		condition.generate_basic_blocks(self, old_block, successor_block)

		# Launch the recursion in two successors if they exist
		if while_block != null then
			if not while_block isa ABlockExpr then block_body.instructions.add(while_block)
			while_block.generate_basic_blocks(self, block_body, block_test)
		end
	end
end

redef class Variable
	# The expressions of AST of this variable depends
	var dep_exprs = new Array[AExpr]

	# The logical dependences between variables
	var dep_variables: nullable Array[Variable]

	# Used to detect cycles
	var dep_cycles: nullable List[Variable]

	fun detect_cycles: nullable List[Variable]
	do
		var deps_copy = dep_exprs.clone

		if dep_cycles == null then
			dep_cycles = new List[Variable]
		end

		var current_path = new List[Variable]
		while not deps_copy.is_empty do
			# Take the first element
			var current = deps_copy.first

			if current isa AVarExpr then
				current_path.add(self)
				current.variable.detect_cycle(current_path)

				var cycle = current.variable.detect_cycle(current_path)
			end

			# Delete current element
			deps_copy.remove(current)
		end

		if dep_cycles != null then
			print "Cycle detected, need to merge"
		end

		# TODO: reparcourir les variables pour fusionner le cycle
		# update_indirect_dependences
		return dep_cycles
	end

	# Detect a cycle on a Variable dependences
	# `path` The current path to this Variable
	fun detect_cycle(path: List[Variable]): nullable List[AExpr]
	do
		var cycle = new List[AExpr]
		for dependence in dep_exprs do
			if dependence isa AVarExpr then
				if path.has(dependence.variable) then
					dependence.variable.dep_cycles.add_all(path)
					dep_cycles.add_all(path)

					# Construct the circuit with all dependences and return
					var circuit = new List[AExpr]
					for v in dependence.variable.dep_cycles do
						circuit.add_all(v.dep_exprs)
					end

					return circuit
				else
					path.add(dependence.variable.as(not null))
				end
			end
		end

		return null
	end

	# The indirect dependences of self
	var indirect_dependences: Array[AExpr] is noinit

	# The blocks in which this variable is assigned
	var assignment_blocks: Array[BasicBlock] = new Array[BasicBlock] is lazy

	# Part of the program where this variable is read
	var read_blocks: Array[BasicBlock] = new Array[BasicBlock] is lazy

	# The original Variable in case of renaming
	var original_variable: Variable = self

	# If true, this variable is a parameter of a method
	var parameter: Bool = false

	# Used for generate versions of variables
	var counter = 0

	# Generate a new version of the self `v` and return it
	# *`expr` The AST node in which the assignment of v is made
	# *`ssa` Current instance of ssa
	fun generate_version(expr: ANode, ssa: SSA): Variable
	do
		# Create a new version of Variable
		var new_version = new Variable(name + counter.to_s)
		new_version.declared_type = expr.as(AVarFormExpr).variable.declared_type
		new_version.dep_exprs.add(expr.as(AVarAssignExpr).n_value)

		ssa.propdef.variables.add(new_version)

		# Recopy the fields into the new version
		new_version.location = expr.location
		new_version.original_variable = original_variable

		# Increment the counter
		counter += 1

		return new_version
	end

	# Update the logical dependences of self
	fun update_logical_dependences: nullable Array[Variable]
	do
		dep_variables = new Array[Variable]
		for dep in dep_exprs do
			if dep isa AVarExpr and not dep.variable.parameter then
				dep_variables.add(dep.variable.as(not null))

				var dep_dep_variables = dep.variable.update_logical_dependences
				for dep_dep in dep_dep_variables do
					dep_variables.add(dep_dep)
				end
			end
		end

		return dep_variables
	end

	fun update_indirect_dependences: Array[AExpr]
	do
		indirect_dependences = new Array[AExpr]
		for dep in dep_exprs do
			if dep isa AVarExpr and not dep.variable.parameter then
				indirect_dependences.add_all(dep.variable.update_indirect_dependences)
			else
				indirect_dependences.add(dep)
			end
		end

		return indirect_dependences
	end
end

# A PhiFunction is a kind of Variable used in SSA-construction,
# it is placed at the beginning of a BasicBlock with many incoming blocks
class PhiFunction
	super Variable

	# The dependences of this variable for SSA-Algorithm
	var dependences = new Array[Couple[Variable, BasicBlock]]

	# The position in the AST of the phi-function
	var block: BasicBlock

	# Set the dependences for the phi-function
	# *`block` BasicBlock in which we go through the dominance-frontier
	# *`v` The variable to look for
	fun add_dependences(block: BasicBlock, v: Variable)
	do
		# Look in which blocks of DF(block) `v` has been assigned
		var dep = new Couple[Variable, BasicBlock](v, block)
		dependences.add(dep)
	end

	# Print the PhiFunction with all its dependences
	redef fun to_s: String
	do
		var s = ""
		s += " dependences = [ "
		for d in dependences do
			s += d.first.to_s + " "
		end
		s += "]"

		return s
	end
end

redef class APropdef
	# The variables contained in the body on this propdef
	var variables: HashSet[Variable] = new HashSet[Variable] is lazy

	# The first basic block of the code
	var basic_block: nullable BasicBlock

	# If true, the basic blocks where generated
	var is_generated: Bool = false

	# Generate all basic blocks for this code
	fun generate_basic_blocks(ssa: SSA) is abstract

	# Contain all AST-parts related to object mechanisms the propdef has:
	# instantiation, method dispatch, attribute access, subtyping-test
	var object_sites: Array[AExpr] = new Array[AExpr]

	# The return variable of the propdef
	# Create an empty variable for the return of the method
	# and treat returns like variable assignments
	var returnvar: Variable = new Variable("returnvar")

	# The basic block of all returns in the method
	var return_block: BasicBlock = new BasicBlock

	# Initialize the environment of the root basic block
	fun init_environment(root_block: BasicBlock)
	do
		for v in variables do
			root_block.environment[v] = new Array[AExpr]
		end
	end

	# Compute the three steps of SSA-algorithm
	# `ssa` A new instance of SSA class initialized with `self`
	fun compute_ssa(ssa: SSA)
	do
		if is_generated then return

		# The returnvar is the only variable of the return block
		return_block.variables.add(returnvar)

		# The first step is to generate the basic blocks
		generate_basic_blocks(ssa)

		# The propdef has no body (abstract)
		if not is_generated then return

		# Once basic blocks were generated, compute SSA algorithm
		compute_environment(ssa)
		ssa_destruction(ssa)

		if mpropdef.name == "foo" then
			var debug = new BlockDebug(new FileWriter.open("basic_blocks.dot"))
			debug.dump(basic_block.as(not null))

			for v in variables do
				print "variable {v} with deps {v.dep_exprs}"
			end
		end
	end

	fun compute_environment(ssa: SSA)
	do
		for v in variables do
			basic_block.versions[v] = v
		end

		basic_block.compute_environment(ssa)
	end

	fun detect_cycles(block: BasicBlock)
	do
		for v in variables do
			v.update_logical_dependences
			v.detect_cycles
		end
	end

	# `ssa` Current instance of SSA
	fun ssa_destruction(ssa: SSA)
	do
		for v in variables do
			# v.update_indirect_dependences
			v.indirect_dependences = v.dep_exprs
			v.dep_exprs = v.indirect_dependences
			for dep in v.indirect_dependences do
				while v.indirect_dependences.count(dep) > 1 do
					v.dep_exprs.remove(dep)
				end
			end
		end
	end
end

redef class AAttrPropdef
	redef fun generate_basic_blocks(ssa: SSA)
	do
		basic_block = new BasicBlock

		# Add the self variable
		if self.selfvariable != null then variables.add(selfvariable.as(not null))

		# Add the return variable
		variables.add(returnvar)

		init_environment(basic_block.as(not null))

		# Recursively goes into the nodes
		if n_block != null then
			n_block.generate_basic_blocks(ssa, basic_block.as(not null), return_block)
			is_generated = true
		end
	end
end

redef class AMethPropdef
	redef fun generate_basic_blocks(ssa: SSA)
	do
		basic_block = new BasicBlock

		# Add the self variable
		if self.selfvariable != null then variables.add(selfvariable.as(not null))

		# If the method has a signature
		if n_signature != null then
			for p in n_signature.n_params do
				# Add parameters to the local variables
				variables.add(p.variable.as(not null))
				p.variable.parameter = true
			end
		end

		# Add the return variable
		variables.add(returnvar)

		init_environment(basic_block.as(not null))

		# Recursively goes into the nodes
		if n_block != null then
			n_block.generate_basic_blocks(ssa, basic_block.as(not null), return_block)
			is_generated = true
		end
	end
end

# Utility class for dump basic block and SSA output to dot files
class BlockDebug
	# The output file
	var file: FileWriter

	# Dump all the hierarchy of BasicBlock from `block` to the leaves
	fun dump(block: BasicBlock)
	do
		# Write the basic blocks hierarchy in output file
		file.write("digraph basic_blocks\n\{\n")
		var i = 0
		file.write(print_block(block, i))
		file.write("\n\}")

		file.close
	end

	# Print all the block recursively from `block` to the leaves
	# *`block` The root BasicBlock
	# *`i` Used for the recursion
	private fun print_block(block: BasicBlock, i: Int): String
	do
		# Precise the type and location of the begin and end of current block
		var s = "block{block.hash.to_s} [shape=record, label="+"\"\{"

		print "Block {block} {block.phi_functions}"
		for instruction in block.instructions do
			print "\t {instruction}"
		end

		print "\n"
		if not block.instructions.is_empty then

			s += "block" + block.to_s.escape_to_dot
			s += "|\{" + block.instructions.first.location.file.filename.to_s + block.instructions.first.location.line_start.to_s
			s += " | " + block.instructions.first.to_s.escape_to_dot

			# Print phi-functions if any
			for phi in block.phi_functions do
				s += " | " + phi.to_s.escape_to_dot + " "
			end

			s += "}|\{" + block.instructions.last.location.file.filename.to_s + block.instructions.last.location.line_start.to_s
			s += " | " + block.instructions.last.to_s.escape_to_dot + "}}\"];"+ "\n"
		else
			s += "block" + block.to_s.escape_to_dot
			s += "|\{" + "null"
			s += " | " + "null"

			# Print phi-functions if any
			for phi in block.phi_functions do
				s += " | " + phi.to_s.escape_to_dot + " "
			end

			s += "}|\{" + "null"
			s += " | " + "null" + "}}\"];"+ "\n"
		end

		i += 1
		block.treated_debug = true

		for b in block.successors do
			# Print edges to successors
			s += "block{block.hash.to_s} -> " + " block{b.hash.to_s};\n"

			# Recursively print child blocks
			if not b.treated_debug then s += print_block(b, i)
		end

		return s
	end
end

redef class AExpr
	# Generate recursively basic block for this expression
	# *`ssa` An instance of the SSA class initialized with the enclosing `APropdef`
	# *`old_block` A basic block not completely filled
	# *`new_block` The BasicBlock with all the following instructions inside
	fun generate_basic_blocks(ssa: SSA, old_block: BasicBlock, new_block: BasicBlock)
	do
	end

	# Visit an expression in a sequence to get variables acces and object-oriented sites
	# *`ssa` The current instance of SSA
	# *`block` The block in which self is included
	fun visit_expression(ssa: SSA, block: BasicBlock)
	do
		# print "NYI {self}"
	end
end

redef class AVarFormExpr
	# The original variable
	var original_variable: nullable Variable = variable
end

redef class AVarExpr
	redef fun visit_expression(ssa, block)
	do
		self.variable.as(not null).read_blocks.add(block)
		block.variables.add(self.variable.as(not null))

		self.variable.as(not null).original_variable = self.variable.as(not null)

		# Save this read site in the block
		block.read_sites.add(self)
		block.variables_sites.add(self)
	end
end

redef class AVardeclExpr
	redef fun visit_expression(ssa, block)
	do
		var decl = self.variable.as(not null)

		decl.original_variable = decl
		block.variables.add(decl)

		if self.n_expr != null then
			self.variable.dep_exprs.add(self.n_expr.as(not null))
			self.n_expr.visit_expression(ssa, block)
		end
	end

	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if not old_block.instructions.has(self) then
			old_block.instructions.add(self)
		end

		ssa.propdef.variables.add(variable.as(not null))
	end
end

redef class AVarAssignExpr
	redef fun visit_expression(ssa, block)
	do
		self.variable.as(not null).assignment_blocks.add(block)
		block.variables.add(self.variable.as(not null))
		self.variable.as(not null).original_variable = self.variable.as(not null)

		block.variables_sites.add(self)

		ssa.propdef.variables.add(self.variable.as(not null))

		self.n_value.visit_expression(ssa, block)
	end

	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if not old_block.instructions.has(self) then
			old_block.instructions.add(self)
		end
	end
end

redef class AVarReassignExpr
	# TODO, split the two instructions
	redef fun visit_expression(ssa, block)
	do
		self.variable.as(not null).assignment_blocks.add(block)
		block.variables.add(self.variable.as(not null))
		self.variable.as(not null).original_variable = self.variable.as(not null)

		# Save this write site in the block
		block.variables_sites.add(self)

		ssa.propdef.variables.add(self.variable.as(not null))
		self.n_value.visit_expression(ssa, block)
	end

	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if not old_block.instructions.has(self) then
			old_block.instructions.add(self)
		end
	end
end

redef class ABreakExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		# Link the old block to the successor one
		old_block.link(new_block)
	end
end

# redef class AContinueExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		return old_block
# 	end
# end

redef class AReturnExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if self.n_expr != null then
			# Store the return expression in the dependences of the dedicated returnvar
			ssa.propdef.returnvar.dep_exprs.add(n_expr.as(not null))
		end

		old_block.link(ssa.propdef.return_block)
	end

	redef fun visit_expression(ssa, block)
	do
		if self.n_expr != null then
			self.n_expr.visit_expression(ssa, block)
		end
	end
end

# redef class AAssertExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		self.n_expr.generate_basic_blocks(ssa, old_block)

# 		# The condition of the assert is the last expression of the previous block
# 		old_block.last = self.n_expr

# 		# The block if the assert fail
# 		var block_false = new BasicBlock

# 		if self.n_else != null then
# 			block_false.first = self.n_else.as(not null)
# 			block_false.last = self.n_else.as(not null)
# 			self.n_else.generate_basic_blocks(ssa, block_false)
# 		else
# 			block_false.first = self
# 			block_false.last = self
# 		end

# 		old_block.link(block_false)

# 		# The block if the assert is true: the execution continue
# 		var block_true = new BasicBlock
# 		block_true.first = self
# 		block_true.last = self

# 		old_block.link(block_true)

# 		return block_true
# 	end
# end

redef class AOrExpr
	redef fun visit_expression(ssa, block)
	do
		self.n_expr.visit_expression(ssa, block)
		self.n_expr2.visit_expression(ssa, block)
	end
end

redef class AImpliesExpr
	redef fun visit_expression(ssa, block)
	do
		self.n_expr.visit_expression(ssa, block)
		self.n_expr2.visit_expression(ssa, block)
	end
end

redef class AAndExpr
	redef fun visit_expression(ssa, block)
	do
		self.n_expr.visit_expression(ssa, block)
		self.n_expr2.visit_expression(ssa, block)
	end
end

redef class ANotExpr
	redef fun visit_expression(ssa, block)
	do
		self.n_expr.visit_expression(ssa, block)
	end
end

redef class AOrElseExpr
	redef fun visit_expression(ssa, block)
	do
		self.n_expr.visit_expression(ssa, block)
		self.n_expr2.visit_expression(ssa, block)
	end
end

redef class AArrayExpr
	redef fun visit_expression(ssa, block)
	do
		for nexpr in self.n_exprs do
			nexpr.visit_expression(ssa, block)
		end
	end
end

redef class ASuperstringExpr
	redef fun visit_expression(ssa, block)
	do
		for nexpr in self.n_exprs do
			nexpr.visit_expression(ssa, block)
		end
	end
end

redef class ACrangeExpr
	redef fun visit_expression(ssa, block)
	do
		self.n_expr.visit_expression(ssa, block)
		self.n_expr2.visit_expression(ssa, block)
	end
end

redef class AOrangeExpr
	redef fun visit_expression(ssa, block)
	do
		self.n_expr.visit_expression(ssa, block)
		self.n_expr2.visit_expression(ssa, block)
	end
end

redef class AIsaExpr
	redef fun visit_expression(ssa, block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.visit_expression(ssa, block)
	end
end

redef class AAsCastExpr
	redef fun visit_expression(ssa, block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.visit_expression(ssa, block)
	end
end

redef class AAsNotnullExpr
	redef fun visit_expression(ssa, block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.visit_expression(ssa, block)
	end
end

redef class AParExpr
	redef fun visit_expression(ssa, block)
	do
		self.n_expr.visit_expression(ssa, block)
	end
end

redef class AOnceExpr
	redef fun visit_expression(ssa, block)
	do
		self.n_expr.visit_expression(ssa, block)
	end
end

redef class ASendExpr
	redef fun visit_expression(ssa, block)
	do
		ssa.propdef.object_sites.add(self)

		# Recursively goes into arguments to find variables if any
		for e in self.raw_arguments do e.visit_expression(ssa, block)

		self.n_expr.visit_expression(ssa, block)
	end
end

# TODO: transform this in two instructions
redef class ASendReassignFormExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)

		ssa.propdef.object_sites.add(self)

		# Recursively goes into arguments to find variables if any
		for e in self.raw_arguments do e.generate_basic_blocks(ssa, old_block, new_block)

		self.n_value.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class ASuperExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		# Recursively goes into arguments to find variables if any
		for arg in self.n_args.n_exprs do arg.generate_basic_blocks(ssa, old_block, new_block)

		ssa.propdef.object_sites.add(self)
	end
end

redef class ANewExpr
	redef fun visit_expression(ssa, block)
	do
		for e in self.n_args.n_exprs do e.visit_expression(ssa, block)

		ssa.propdef.object_sites.add(self)
	end
end

redef class AAttrExpr
	redef fun visit_expression(ssa, block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.visit_expression(ssa, block)
	end
end

redef class AAttrAssignExpr
	redef fun visit_expression(ssa, block)
	do
		ssa.propdef.object_sites.add(self)
		self.n_value.visit_expression(ssa, block)

		self.n_expr.visit_expression(ssa, block)
	end
end

redef class AAttrReassignExpr
	# TODO: separate the instructions
	redef fun visit_expression(ssa, block)
	do
		ssa.propdef.object_sites.add(self)
		self.n_value.visit_expression(ssa, block)

		self.n_expr.visit_expression(ssa, block)
	end
end

redef class AIssetAttrExpr
	redef fun visit_expression(ssa, block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.visit_expression(ssa, block)
	end
end

redef class ABlockExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		for expr in n_expr do
			old_block.instructions.add(expr)
		end

		# Recursively continue in the body of the block
		for i in [0..self.n_expr.length[ do
			# old_block.instructions.add(n_expr[i])
			self.n_expr[i].generate_basic_blocks(ssa, old_block, new_block)
		end
	end

	redef fun visit_expression(ssa: SSA, block: BasicBlock)
	do
		for expr in n_expr do
			expr.visit_expression(ssa, block)
		end
	end
end

redef class AIfExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if not old_block.instructions.has(self) then old_block.instructions.add(self)

		var index = old_block.instructions.index_of(self)
		var to_remove = new List[AExpr]
		old_block.instructions.remove(self)

		# Move the instructions after the if to the new block
		for i in [index..old_block.instructions.length[ do
			to_remove.add(old_block.instructions[i])
			new_block.variables_sites.add_all(old_block.variables_sites)
			new_block.instructions.add(old_block.instructions[i])
		end

		for instruction in to_remove do
			old_block.instructions.remove(instruction)
		end

		# Generate a if structure for the blocks
		ssa.generate_if(old_block, n_expr, n_then, n_else, new_block)
	end

	redef fun visit_expression(ssa: SSA, block: BasicBlock)
	do
		n_expr.visit_expression(ssa, block)
		if n_then != null then n_then.visit_expression(ssa, block)
		if n_else != null then n_else.visit_expression(ssa, block)
	end
end

redef class AIfexprExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if not old_block.instructions.has(self) then old_block.instructions.add(self)

		var index = old_block.instructions.index_of(self)
		var to_remove = new List[AExpr]
		old_block.instructions.remove(self)

		# Move the instructions after the if to the new block
		for i in [index..old_block.instructions.length[ do
			to_remove.add(old_block.instructions[i])
			new_block.instructions.add(old_block.instructions[i])
		end

		for instruction in to_remove do
			old_block.instructions.remove(instruction)
		end

		# Generate a if structure for the blocks
		ssa.generate_if(old_block, n_expr, n_then, n_else, new_block)
	end

	redef fun visit_expression(ssa: SSA, block: BasicBlock)
	do
		n_expr.visit_expression(ssa, block)
		n_then.visit_expression(ssa, block)
		n_else.visit_expression(ssa, block)
	end
end

redef class ADoExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		self.n_block.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class AWhileExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if not old_block.instructions.has(self) then old_block.instructions.add(self)

		var index = old_block.instructions.index_of(self)
		var to_remove = new List[AExpr]
		old_block.instructions.remove(self)

		# Move the instructions after the if to the new block
		for i in [index..old_block.instructions.length[ do
			to_remove.add(old_block.instructions[i])
			new_block.instructions.add(old_block.instructions[i])
		end

		for instruction in to_remove do
			old_block.instructions.remove(instruction)
		end

		# Generate a while structure
		ssa.generate_while(old_block, n_expr, n_block, new_block)
	end
end

redef class ALoopExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		self.n_block.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class AForExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if not old_block.instructions.has(self) then old_block.instructions.add(self)

		var index = old_block.instructions.index_of(self)
		var to_remove = new List[AExpr]
		old_block.instructions.remove(self)

		# Move the instructions after the if to the new block
		for i in [index..old_block.instructions.length[ do
			to_remove.add(old_block.instructions[i])
			new_block.instructions.add(old_block.instructions[i])
		end

		for instruction in to_remove do
			old_block.instructions.remove(instruction)
		end

		# Collect the variables declared in the for
		for v in variables do
			ssa.propdef.variables.add(v)
		end

		# Generate a for structure (similar to a while loop)
		ssa.generate_while(old_block, n_expr, n_block, new_block)
	end
end
