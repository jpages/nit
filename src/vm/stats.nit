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

	fun get_stats
	do
		# Statistics about immutable attributes
		for m in model.mmodules do
			for cd in m.mclassdefs do
				for pd in cd.mpropdefs do
					# See if attributes are initialized only in their constructors
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
