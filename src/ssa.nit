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

	# The iterated dominance frontier of this block
	# i.e. the set of blocks this block dominate directly or indirectly
	var dominance_frontier: Array[BasicBlock] = new Array[BasicBlock] is lazy

	# Compute the environment of the current block
	fun compute_environment(ssa: SSA)
	do
		# By default, clone a predecessor environment,
		# If there is no predecessor, this is the root_block and just initialize it
		if not predecessors.is_empty then
			environment = predecessors.first.clone_environment
		end

		# #DEBUG
		print "environment of {self} {instructions}"
		for key,value in environment do
			print "\t {key} -> {value}"
		end

		var other_predecessors = new Array[BasicBlock]
		other_predecessors.add_all(predecessors)
		other_predecessors.remove_at(0)

		# Then add all variables the cloned environment does not have
		for other in other_predecessors do
			for key, value in other.environment do
				if not environment.has_key(key) then
					environment[key] = new Array[AExpr]
					environment[key].add_all(value)
				end
			end
		end

		# Add all new variables to the environment
		for instruction in instructions do
			if instruction isa AVardeclExpr then
				# Add a new Variable to the environment
				environment[instruction.variable.as(not null)] = new Array[AExpr]

				# If there is an initial value
				if instruction.n_expr != null then
					environment[instruction.variable.as(not null)].add(instruction.n_expr.as(not null))
				end
			end
		end

		# Handle the PhiFunction
		for phi in phi_functions do
			# For each phi, merge dependences
			for dependence in phi.dependences do
				# For each variable in dependence, copy its value in a previous block and put it inside current environment
				if not environment.has_key(dependence.first) then
					environment[dependence.first] = new Array[AExpr]
				end

				if dependence.second.environment.has_key(dependence.first) then
					environment[dependence.first].add_all(dependence.second.environment[dependence.first])
				else
					# TODO: Problem
					print "Problem with {dependence.second.environment} {dependence.first}"

					for key, value in dependence.second.environment do
						print "\t {key} -> {value}"
					end
				end
			end
		end

		for site in variables_sites do
			if site isa AVarAssignExpr then
				# We need to create a new version of the variable
				var new_version = site.variable.original_variable.generate_version(site, ssa)

				# Then we replace the old version by the new one in the environment
				environment[site.variable.as(not null)].remove_all
				environment[site.variable.as(not null)].add(site.n_value)

				# TODO: essayer d'ajouter la nouvelle version à l'environnement
				environment[new_version] = new_version.dep_exprs
			else if site isa AVarExpr then
				if not environment.has_key(site.variable) then
					print "\t problem in variables_sites with {site.variable.as(not null)} {instructions}"

					ssa.propdef.dump_tree
				end
				# Just copy the value inside the environment in the variable
				site.variable.dep_exprs = environment[site.variable].clone
			end
		end

		# Finally, launch the recursion in successors block
		for block in successors do
			block.compute_environment(ssa)
		end
	end

	# Return a new environment which is a copy of the current one
	fun clone_environment: HashMap[Variable, Array[AExpr]]
	do
		var clone = new HashMap[Variable, Array[AExpr]]

		for variable, values in environment do
			clone[variable] = new Array[AExpr]
			clone[variable].add_all(values)
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

	# Used to handle recursions by treating only one time each block
	var treated: Bool = false

	# Each block must be treated for each version of Variable
	var treated_phi = new HashSet[Variable]

	# Used to dump the BasicBlock to dot
	var treated_debug: Bool = false

	# If true, the iterated dominance frontier of this block has been computed
	var df_computed: Bool = false

	# Indicate the BasicBlock is newly created and needs to be updated
	var need_update: Bool = false

	# Indicates the BasicBlock needs to be linked to a successor
	var need_link: Bool = false

	# Indicate if the variables renaming step has been made for this block
	var is_renaming: Bool = false

	# The variables that are accessed in this block
	var variables = new Array[Variable] is lazy

	# The PhiFunction this block contains at the beginning
	var phi_functions = new Array[PhiFunction] is lazy
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
			then_branch.generate_basic_blocks(self, block_then, successor_block)
		end

		if else_branch != null then
			else_branch.generate_basic_blocks(self, block_else, successor_block)
		end

	end
end

redef class Variable
	# The expressions of AST of this variable depends
	var dep_exprs = new Array[AExpr]

	# The blocks in which this variable is assigned
	var assignment_blocks: Array[BasicBlock] = new Array[BasicBlock] is lazy

	# Part of the program where this variable is read
	var read_blocks: Array[BasicBlock] = new Array[BasicBlock] is lazy

	# The stack of this variable, used for SSA renaming
	var stack = new Array[Variable] is lazy

	# The original Variable in case of renaming
	var original_variable: nullable Variable = self

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
		new_version.original_variable = original_variable.as(not null)

		# Increment the counter
		counter += 1

		return new_version
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
	# *`v` The variable to looking for
	fun add_dependences(block: BasicBlock, v: Variable)
	do
		# Look in which blocks of DF(block) `v` has been assigned
		for b in block.predecessors do
			# if v.assignment_blocks.has(b) then
				var dep = new Couple[Variable, BasicBlock](v, b)
				dependences.add(dep)
			# end
		end
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
		compute_phi(ssa)
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
		basic_block.compute_environment(ssa)
	end

	# Compute the first phase of SSA algorithm: placing phi-functions
	fun compute_phi(ssa: SSA)
	do
		var root_block = basic_block.as(not null)

		# Compute the iterated dominance frontier of the graph of basic blocks
		root_block.compute_df

		# Places where a phi-function is added per variable
		var phi_blocks = new HashMap[Variable, Array[BasicBlock]]

		# For each variables in the propdef
		for v in variables do
			var phi_variables = new Array[BasicBlock]

			var blocks = new Array[BasicBlock]
			blocks.add_all(v.assignment_blocks)

			# While we have not treated each part defining `v`
			while not blocks.is_empty do
				# Remove a block from the array
				var block = blocks.shift

				# For each block in the dominance frontier of `block`
				for df in block.dominance_frontier do
					# If we have not yet put a phi-function at the beginning of this block
					if not phi_variables.has(df) then
						phi_variables.add(df)

						# Create a new phi-function and set its dependences
						var phi = new PhiFunction("phi", df)
						phi.add_dependences(df, v)
						phi.block = df
						phi.original_variable = phi
						phi.declared_type = v.declared_type

						# Indicate this phi-function is assigned in this block
						phi.assignment_blocks.add(block)
						ssa.phi_functions.add(phi)

						# Add a phi-function at the beginning of df for variable v
						df.phi_functions.add(phi)

						if not v.read_blocks.has(df) or not v.assignment_blocks.has(df) then blocks.add(df)
					end
				end
			end

			# Add `phi-variables` to the global map
			phi_blocks[v] = phi_variables
		end
	end

	fun generate_name(v: Variable, counter: HashMap[Variable, Int], expr: ANode, ssa: SSA): Variable
	do
		var original_variable = v.original_variable.as(not null)

		var i = counter[original_variable]

		var new_version: Variable

		# Create a new version of Variable
		if original_variable isa PhiFunction then
			var block = original_variable.block
			new_version = new PhiFunction(original_variable.name + i.to_s, block)
			new_version.dependences.add_all(original_variable.dependences)
			ssa.phi_functions.add(new_version)
		else
			new_version = new Variable(original_variable.name + i.to_s)
			new_version.declared_type = expr.as(AVarFormExpr).variable.declared_type
			variables.add(new_version)
		end

		# Recopy the fields into the new version
		new_version.location = expr.location
		new_version.original_variable = original_variable

		# Push a new version on the stack
		original_variable.stack.add(new_version)
		counter[v] = i + 1

		return new_version
	end

	# Transform SSA-representation into an executable code (delete phi-functions)
	# `ssa` Current instance of SSA
	fun ssa_destruction(ssa: SSA)
	do
		var builder = new ASTBuilder(mpropdef.mclassdef.mmodule, mpropdef.mclassdef.bound_mtype)

		# Iterate over all phi-functions
		for phi in ssa.phi_functions do
			# Collect all the dep_exprs of several variables in the phi
			var phi_deps = new List[AExpr]
			for dependence in phi.dependences do
				for dep_expr in dependence.first.dep_exprs do
					if not phi_deps.has(dep_expr) then phi_deps.add(dep_expr)
				end
			end

			for dep in phi.dependences do
				dep.first.dep_exprs = phi_deps.to_a

				# dep.second is the block where we need to create a varassign
				var var_read = builder.make_var_read(dep.first, dep.first.declared_type.as(not null))
				var nvar = builder.make_var_assign(dep.first, var_read)

				# Add the varassign to all predecessor blocks
				var previous_block = dep.second
				previous_block.instructions.add(nvar)

				# previous_block.variables_sites.add(var_read)
				# previous_block.write_sites.add(nvar)

				propagate_dependences(dep.first, phi.block, phi_deps)
				ssa.propdef.variables.add(dep.first)
			end
		end
	end

	# Propagate the dependences of the phi-functions into following variables
	# `phi` The PhiFunction
	# `block` Current block where we propagate dependences
	fun propagate_dependences(variable: Variable, block: BasicBlock, dep_exprs: List[AExpr])
	do
		# Treat each block once
		if block.treated_phi.has(variable) then return

		# For each variable access site in the block
		for site in block.variables_sites do
			if site isa AVarExpr then
				# Propagate the dependences of the phi-function in variables after the phi
				for expr in dep_exprs do
					if not site.variable.dep_exprs.has(expr) then
						site.variable.dep_exprs.add(expr)
					end
				end
			else
				# The site is a variable write, we stop the propagation
				return
			end
		end

		block.treated_phi.add(variable)

		# If we do not meet a variable write, continue the propagation
		for b in block.successors do propagate_dependences(variable, b, dep_exprs)
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
			# s += "|\{" + block.instructions.first.location.file.filename.to_s + block.instructions.first.location.line_start.to_s
			s += "|\{" + block.instructions.first.to_s
			s += " | " + block.instructions.first.to_s.escape_to_dot

			# Print phi-functions if any
			for phi in block.phi_functions do
				s += " | " + phi.to_s.escape_to_dot + " "
			end

			# s += "}|\{" + block.instructions.last.location.file.filename.to_s + block.instructions.last.location.line_start.to_s
			s += "}|\{" + block.instructions.last.to_s

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
end

redef class AVarFormExpr
	# The original variable
	var original_variable: nullable Variable = variable
end

redef class AVarExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		self.variable.as(not null).read_blocks.add(old_block)
		old_block.variables.add(self.variable.as(not null))

		self.variable.as(not null).original_variable = self.variable.as(not null)
		# Save this read site in the block
		old_block.read_sites.add(self)
		old_block.variables_sites.add(self)
	end
end

redef class AVardeclExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		var decl = self.variable.as(not null)

		# Add the corresponding variable to the enclosing mpropdef
		ssa.propdef.variables.add(decl)

		decl.original_variable = decl
		# decl.assignment_blocks.add(old_block)
		old_block.variables.add(decl)

		if self.n_expr != null then
			self.variable.dep_exprs.add(self.n_expr.as(not null))
			self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
		end
	end
end

redef class AVarAssignExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		self.variable.as(not null).assignment_blocks.add(old_block)
		old_block.variables.add(self.variable.as(not null))
		self.variable.as(not null).original_variable = self.variable.as(not null)

		old_block.variables_sites.add(self)

		ssa.propdef.variables.add(self.variable.as(not null))

		self.n_value.generate_basic_blocks(ssa, old_block, new_block)
	end
end

# TODO, split the two instructions
redef class AVarReassignExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		self.variable.as(not null).assignment_blocks.add(old_block)
		old_block.variables.add(self.variable.as(not null))
		self.variable.as(not null).original_variable = self.variable.as(not null)

		# Save this write site in the block
		old_block.variables_sites.add(self)

		ssa.propdef.variables.add(self.variable.as(not null))
		self.n_value.generate_basic_blocks(ssa, old_block, new_block)
	end
end

# redef class ABreakExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		# Finish the old block
# 		old_block.last = self

# 		return old_block
# 	end
# end

# redef class AContinueExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		return old_block
# 	end
# end

# TODO, terminate the previous block and stop the recursion
redef class AReturnExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		# The return just set the current block and stop the recursion
		if self.n_expr != null then
			self.n_expr.generate_basic_blocks(ssa, old_block, new_block)

			# Store the return expression in the dependences of the dedicated returnvar
			ssa.propdef.returnvar.dep_exprs.add(n_expr.as(not null))
		end

		old_block.link(ssa.propdef.return_block)
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

# redef class AOrExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		self.n_expr.generate_basic_blocks(ssa, old_block)
# 		return self.n_expr2.generate_basic_blocks(ssa, old_block)
# 	end
# end

# redef class AImpliesExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		self.n_expr.generate_basic_blocks(ssa, old_block)
# 		return self.n_expr2.generate_basic_blocks(ssa, old_block)
# 	end
# end

# redef class AAndExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		self.n_expr.generate_basic_blocks(ssa, old_block)
# 		return self.n_expr2.generate_basic_blocks(ssa, old_block)
# 	end
# end

# redef class ANotExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		return self.n_expr.generate_basic_blocks(ssa, old_block)
# 	end
# end

# redef class AOrElseExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		self.n_expr.generate_basic_blocks(ssa, old_block)
# 		return self.n_expr2.generate_basic_blocks(ssa, old_block)
# 	end
# end

# redef class AArrayExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		for nexpr in self.n_exprs do
# 			old_block = nexpr.generate_basic_blocks(ssa, old_block)
# 		end

# 		return old_block
# 	end
# end

# redef class ASuperstringExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		for nexpr in self.n_exprs do old_block = nexpr.generate_basic_blocks(ssa, old_block)

# 		return old_block
# 	end
# end

# redef class ACrangeExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		self.n_expr.generate_basic_blocks(ssa, old_block)
# 		return self.n_expr2.generate_basic_blocks(ssa, old_block)
# 	end
# end

# redef class AOrangeExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		self.n_expr.generate_basic_blocks(ssa, old_block)
# 		return self.n_expr2.generate_basic_blocks(ssa, old_block)
# 	end
# end

redef class AIsaExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class AAsCastExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class AAsNotnullExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class AParExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class AOnceExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class ASendExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		# A call does not finish the current block,
		# because we create intra-procedural basic blocks here
		ssa.propdef.object_sites.add(self)

		# Recursively goes into arguments to find variables if any
		for e in self.raw_arguments do e.generate_basic_blocks(ssa, old_block, new_block)

		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
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
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		for e in self.n_args.n_exprs do e.generate_basic_blocks(ssa, old_block, new_block)

		ssa.propdef.object_sites.add(self)
	end
end

redef class AAttrExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class AAttrAssignExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		ssa.propdef.object_sites.add(self)
		self.n_value.generate_basic_blocks(ssa, old_block, new_block)

		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
	end
end

# TODO: separate the instructions
redef class AAttrReassignExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		ssa.propdef.object_sites.add(self)
		self.n_value.generate_basic_blocks(ssa, old_block, new_block)

		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
	end
end

redef class AIssetAttrExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		ssa.propdef.object_sites.add(self)

		self.n_expr.generate_basic_blocks(ssa, old_block, new_block)
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
			self.n_expr[i].generate_basic_blocks(ssa, old_block, new_block)
		end
	end
end

redef class AIfExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if not old_block.instructions.has(self) then old_block.instructions.add(self)

		var index = old_block.instructions.index_of(self)
		var to_remove = new List[AExpr]

		print "Old_block = {old_block.instructions} to_remove {to_remove}"
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
end

redef class AIfexprExpr
	redef fun generate_basic_blocks(ssa, old_block, new_block)
	do
		if not old_block.instructions.has(self) then old_block.instructions.add(self)

		var index = old_block.instructions.index_of(self)
		var to_remove = new List[AExpr]

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
end

# redef class ADoExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		old_block.last = self

# 		# The beginning of the block is the first instruction
# 		var block = new BasicBlock
# 		block.first = self.n_block.as(not null)
# 		block.last = self.n_block.as(not null)

# 		old_block.link(block)
# 		return self.n_block.generate_basic_blocks(ssa, block)
# 	end
# end

# redef class AWhileExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		old_block.last = self

# 		# The beginning of the block is the test of the while
# 		var block = new BasicBlock
# 		block.first = self.n_expr
# 		block.last = self.n_block.as(not null)

# 		old_block.link(block)

# 		self.n_expr.generate_basic_blocks(ssa, old_block)
# 		self.n_block.generate_basic_blocks(ssa, block)

# 		# Link the inside of the block to the previous block
# 		block.link_special(old_block)

# 		# Create a new Block after the while
# 		var new_block = new BasicBlock
# 		new_block.first = self
# 		new_block.last = self
# 		new_block.need_update = true
# 		new_block.need_link = true

# 		old_block.link_special(new_block)

# 		return new_block
# 	end
# end

# redef class ALoopExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		old_block.last = self

# 		# The beginning of the block is the first instruction
# 		var block = new BasicBlock
# 		block.first = self.n_block.as(not null)
# 		block.last = self.n_block.as(not null)

# 		old_block.link(block)
# 		self.n_block.generate_basic_blocks(ssa, block)

# 		return block
# 	end
# end

# redef class AForExpr
# 	redef fun generate_basic_blocks(ssa, old_block)
# 	do
# 		old_block.last = self

# 		# The beginning of the block is the first instruction
# 		var block = new BasicBlock
# 		block.first = self.n_expr
# 		block.last = self.n_block.as(not null)

# 		# Visit the test of the if
# 		self.n_expr.generate_basic_blocks(ssa, block)

# 		# Collect the variables declared in the for
# 		for v in variables do
# 			ssa.propdef.variables.add(v)
# 		end

# 		old_block.link(block)

# 		block.link(old_block)

# 		var new_block = new BasicBlock
# 		new_block.first = self
# 		new_block.last = self

# 		new_block.need_update = true
# 		new_block.need_link = true

# 		return new_block
# 	end
# end
