# This file is part of NIT ( http://www.nitlanguage.org ).
#
# Copyright 2016 Julien Pagès <julien.pages@lirmm.fr>
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

# A module of optimizations related to concrete types in the nitvm
module concrete_types

import virtual_machine

# A class to gather final classes and concrete attribute types,
# This class is not compatible with dynamic loading, thus it emulates
# informations of a hypothetical annotated bytecode
class GlobalAnalysis
	# The modelbuilder of the program
	var modelbuilder: ModelBuilder

	# The mainmodule of the program
	var mainmodule: MModule

	# The set of all final classes of the executed program
	var final_classes = new List[MClass]

	# The classes that are not leaves of the hierarchy
	var classes = new List[MClass]

	# The set of immutable attributes of the program,
	# attributes that are only initialized in the class constructor (or inline with initial value)
	var attributes = new List[MAttribute]

	# The set of immutable attributes
	var immutable_attributes = new HashSet[MAttribute]

	# The set of mutable attributes of the program
	var mutable_attributes = new HashSet[MAttribute]

	fun get_stats
	do
		var visitor = new FinalAttributeVisitor(self)

		# Detect final classes
		for mod in modelbuilder.model.mmodules do
			for classdef in mod.mclassdefs do
				# If the class is a leaf of the hierarchy
				if classdef.mclass.in_hierarchy(mainmodule).direct_smallers.length == 0 then
					# Add it to the collection
					final_classes.add(classdef.mclass)

					if classdef.mclass.name == "NativeArray" or classdef.mclass.name == "NativeString" then
						classdef.mclass.is_final = true
					end

					# To be more realistic, just annotate is_final classes which are introduced in the AST ou parser
					if classdef.mclass.intro_mmodule.name == "parser" or classdef.mclass.intro_mmodule.name == "parser_nodes" then
						classdef.mclass.is_final = true
					end
				else
					classes.add(classdef.mclass)
				end
			end
		end

		# Collect about immutable attributes
		for m in modelbuilder.model.mmodules do
			for cd in m.mclassdefs do
				for mpropdef in cd.mpropdefs do
					# For each MPropdef of the code
					var node = modelbuilder.mpropdef2node(mpropdef)

					# See if attributes are initialized only in their constructors
					if node != null and node isa APropdef then
						if node isa AAttrPropdef then
							attribute_declaration(node)
						end

						# Visit all propdefs
						visitor.propdef = node
						node.visit_all(visitor)
					end
				end
			end
		end
	end

	# Get the concrete type of the initial value of this attribute
	fun attribute_declaration(node: AAttrPropdef)
	do
		# Get all the annotations attached to this AAttrPropdef
		if node.n_annotations != null then
			for annotation in node.n_annotations.n_items do
				if annotation.name == "writable" then
					# If the setter of the attribute is public for all modules,
					# we can not use its concrete types
					node.mpropdef.mproperty.has_concrete_types = false
					return
				end
			end
		end

		if node.n_expr != null then
			# Only if the initial value is a new
			if node.n_expr isa ANewExpr then
				if not node.mpropdef.mproperty.assignments.has(node.n_expr.as(not null)) then
					node.mpropdef.mproperty.assignments.add(node.n_expr.as(not null))
				end
			else if node.n_expr.mtype isa MClassType then
				# If the static type of the Right part of assignment is a final type
				var mclass = node.n_expr.mtype.as(MClassType).mclass
				if mclass.is_final then
					node.mpropdef.mproperty.concrete_types.add(mclass)
				end
			else
				# The attribute do not have concrete types
				node.mpropdef.mproperty.has_concrete_types = false
			end
		end
	end
end

# A visitor used to collect concrete types of attributes and detect immutable attributes
class FinalAttributeVisitor
	super Visitor

	var propdef: nullable APropdef

	var concrete_types: GlobalAnalysis

	redef fun visit(n)
	do
		if n isa AAttrFormExpr then
			var mattribute = n.mproperty.as(not null)

			# By default the attribute is immutable
			if not concrete_types.mutable_attributes.has(mattribute) then
				concrete_types.immutable_attributes.add(mattribute)
			end

			# If the attribute is written
			if n isa AAttrAssignExpr or n isa AAttrReassignExpr then

				# If the Attribute is written in another class of its introduction class,
				# it is mutable
				if mattribute.intro_mclassdef.mclass != propdef.mpropdef.mclassdef.mclass then
					concrete_types.mutable_attributes.add(mattribute)

					# If needed, remove it from immutable attributes
					if concrete_types.immutable_attributes.has(mattribute) then
						concrete_types.immutable_attributes.remove(mattribute)
					end
				else
					# Written in a property which is not a constructor
					if propdef.mpropdef.as(MMethodDef).initializers.is_empty then
						concrete_types.immutable_attributes.remove(mattribute)
						concrete_types.mutable_attributes.add(mattribute)
					end
				end
			end

			# Collect the right part of assignments for this attribute
			if n isa AAttrAssignExpr then
				if n.n_value isa ANewExpr then
					mattribute.assignments.add(n.n_value)
				else if n.n_value.mtype isa MClassType then
					# If the static type of the Right part of assignment is a final type
					var mclass = n.n_value.mtype.as(MClassType).mclass
					if mclass.is_final then
						mattribute.concrete_types.add(mclass)
					end
				else
					mattribute.has_concrete_types = false
				end
			else if n isa AAttrReassignExpr then
				if n.n_value isa ANewExpr then
					mattribute.assignments.add(n.n_value)
				else if n.n_value.mtype isa MClassType then
					# If the static type of the Right part of assignment is a final type
					var mclass = n.n_value.mtype.as(MClassType).mclass
					if mclass.is_final then
						mattribute.concrete_types.add(mclass)
					end
				else
					mattribute.has_concrete_types = false
				end
			end
		end

		# The attribute can be set with a call to its setter
		if n isa ASendExpr then
			var called_node_ast = concrete_types.modelbuilder.mpropdef2node(n.callsite.mpropdef)
			var is_attribute = called_node_ast isa AAttrPropdef

			# A call to an accessor
			if is_attribute then
				# If the accessor is a setter
				if n.callsite.msignature.mparameters.length != 0 then
					var mattribute = called_node_ast.as(AAttrPropdef).mpropdef.as(not null).mproperty

					# We add only the right part of assignement if this is a new
					# TODO: handle the case of primitive types
					if n.raw_arguments[0] isa ANewExpr then
						mattribute.assignments.add(n.raw_arguments[0])
					else if n.raw_arguments[0].mtype isa MClassType then
						# If the static type of the Right part of assignment is a final type
						var mclass = n.raw_arguments[0].mtype.as(MClassType).mclass
						if mclass.is_final then
							mattribute.concrete_types.add(mclass)
						end
					else
						mattribute.has_concrete_types = false
					end
				end
			end
		end

		# Recursively visit all children
		n.visit_all(self)
	end
end

redef class MAttribute
	# All right parts of assignments for this attribute
	var assignments = new List[AExpr]

	# Indicate if we can use the concrete types of this attribute,
	# if false, then the attribute do not have concrete types
	var has_concrete_types = true

	# The list of concrete types of the Attribute
	var concrete_types = new List[MClass]

	# Compute the closed-world concrete types for this global attribute and return them
	fun compute_concretes: List[MClass]
	do
		if not concrete_types.is_empty then return concrete_types

		for assignment in assignments do
			var mclass = assignment.as(ANewExpr).mtype.as(MClassType).mclass

			if not concrete_types.has(mclass) then concrete_types.add(mclass)
		end

		return concrete_types
	end
end

redef class MClass

	# Indicate if this class does not have subclasses
	var is_final = false
end

# Represents concrete types of an expression
class ConcreteTypes
	super List[MClass]

	# Indicate if all concrete types of the expression are immutables,
	# (coming from a new, a readsite, a final expression)
	var immutable: Bool = false is writable

	# Redef to not duplicate concrete types
	redef fun add(mclass)
	do
		if not has(mclass) then super
	end
end
