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

# Make sure the computation of position methods and attributes is correct
module test_positions

import virtual_machine

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule: MModule, arguments: Array[String])
	do
		super

		self.mainmodule = mainmodule
		verify_positions
	end

	# The mainmodule of the program
	var mainmodule: MModule

	# All the loaded classes after the execution of the program
	var loaded_classes: HashSet[MClass] = new HashSet[MClass]

	fun verify_positions
	do
		# Collect all loaded classes
		for m in model.mmodules do
			for cd in m.mclassdefs do
				if cd.mclass.abstract_loaded then loaded_classes.add(cd.mclass)
			end
		end

		print "The program load {loaded_classes.length} classes"

		# Verify the position of all these classes
		for mclass in loaded_classes do
			# If `mclass` is supposed to be in invariant position in all subclasses
			if mclass.position_methods > 0 then
				assert test_unique_position_methods(mclass, mclass)
			else if mclass.position_methods < 0 then
				# Check that the position is really invariant under this class
				print "Multiple positions {test_multiple_positions_methods(mclass, mclass)}"
			end

			if mclass.position_attributes > 0 then
				assert test_unique_position_attributes(mclass, mclass)
			end
		end
	end

	# Test for methods
	fun test_unique_position_methods(test_class: MClass, mclass: MClass): Bool
	do
		if mclass.positions_methods.has_key(test_class) then return false

		for subclass in mclass.subclasses do
			# Verify that this class has not in its hashmap `mclass`
			if subclass.positions_methods.has_key(test_class) then return false

			# Recursively continue on subclasses
			test_unique_position_methods(test_class, subclass)
		end

		return true
	end

	# Test for methods
	fun test_unique_position_attributes(test_class: MClass, mclass: MClass): Bool
	do
		if mclass.positions_attributes.has_key(test_class) then return false

		for subclass in mclass.subclasses do
			# Verify that this class has not in its hashmap `mclass`
			if subclass.positions_attributes.has_key(test_class) then return false

			# Recursively continue on subclasses
			test_unique_position_attributes(test_class, subclass)
		end

		return true
	end

	fun test_multiple_positions_methods(test_class: MClass, mclass: MClass): Bool
	do
		# The position found in `mclass` HashMap
		var pos_map = mclass.positions_methods[test_class]

		if pos_map != test_class.positions_methods[test_class] then return true

		for subclass in mclass.subclasses do
			test_multiple_positions_methods(test_class, subclass)
		end

		return false
	end
end
