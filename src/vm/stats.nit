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

# Statistics on final classes and immutable attributes
module stats

import virtual_machine

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule: MModule, arguments: Array[String])
	do
		super

		self.mainmodule = mainmodule
		get_stats
		treat_stats
	end

	var mainmodule: MModule

	# The set of all final classes of the executed program
	var final_classes = new HashSet[MClass]

	# The classes that are not leaves of the hierarchy
	var classes = new HashSet[MClass]

	# The set of immutable attributes of the program,
	# attributes that are only initialized in the class constructor (or inline with initial value)
	var immutable_attributes = new HashSet[MAttribute]

	# The set of mutable attributes of the program
	var mutable_attributes = new HashSet[MAttribute]

	fun get_stats
	do
		var visitor = new FinalAttributeVisitor

		# Statistics about immutable attributes
		for m in model.mmodules do
			for cd in m.mclassdefs do
				for mpropdef in cd.mpropdefs do
					# For each MPropdef of the code
					var node = mpropdef2node(mpropdef)

					# See if attributes are initialized only in their constructors
					if node != null and node isa APropdef then
						# Visit all propdefs
						visitor.propdef = node.as(APropdef)
						node.visit_all(visitor)
					end
				end
			end
		end

		# Statistics about final classes
		for mod in model.mmodules do
			for classdef in mod.mclassdefs do
				# If the class is a leaf of the hierarchy
				if classdef.mclass.in_hierarchy(mainmodule).direct_smallers.length == 0 then
					# Add it to the collection
					final_classes.add(classdef.mclass)
				else
					classes.add(classdef.mclass)
				end
			end
		end
	end

	fun treat_stats
	do
		print "Number of leaves : {final_classes.length}"
		print "Number of classes with subclasses : {classes.length}"

		print "Number of classes : {final_classes.length + classes.length}"
	end
end

class FinalAttributeVisitor
	super Visitor

	var propdef: nullable APropdef

	redef fun visit(n)
	do
		if n isa AAttrFormExpr then
			# If the attribute is written
			if n isa AAttrAssignExpr or n isa AAttrReassignExpr then
				assert n isa AAttrFormExpr
				print "Acces to {n.mproperty.as(not null)} in {propdef.mpropdef.full_name}"
			end
		end

		# Recursively visit all children
		n.visit_all(self)
	end
end