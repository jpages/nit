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

# Optimization of the nitvm, compute implementations
module vm_optimizations

import preexistence

redef class VirtualMachine
	# Add optimization of the method dispatch
	redef fun callsite(callsite, arguments)
	do
		var initializers = callsite.as(not null).mpropdef.initializers
		if initializers.is_empty then return send_optimize(callsite.as(not null), arguments)

		var recv = arguments.first
		var i = 1
		for p in initializers do
			if p isa MMethod then
				var args = [recv]
				for x in p.intro.msignature.as(not null).mparameters do
					args.add arguments[i]
					i += 1
				end
				self.send(p, args)
			else if p isa MAttribute then
				assert recv isa MutableInstance
				write_attribute(p, recv, arguments[i])
				i += 1
			else abort
		end
		assert i == arguments.length

		return send_optimize(callsite.as(not null), [recv])
	end

	# Try to have the most efficient implementation of the method dispatch
	fun send_optimize(callsite: CallSite, args: Array[Instance]): nullable Instance
	do
		var recv = args.first
		var mtype = recv.mtype
		var ret = send_commons(callsite.mproperty, args, mtype)
		if ret != null then return ret

		if callsite.status == 0 then callsite.optimize(recv)

		var propdef
		if callsite.status == 1 then
			propdef = method_dispatch_sst(recv.vtable.as(not null).internal_vtable, callsite.offset)
		else
			propdef = method_dispatch_ph(recv.vtable.as(not null).internal_vtable, recv.vtable.as(not null).mask,
				callsite.id, callsite.offset)
		end

		#TODO : we need recompilations here
		callsite.status = 0

		# Test with new mechanisms
		if callsite.mocallsite != null then
			var impl = callsite.mocallsite.get_impl(sys.vm)

			# Reset the implementation
			callsite.mocallsite.impl = null
			var impl2 = callsite.mocallsite.get_impl(sys.vm)

			if impl.exec_method(recv) != propdef then
				print "\n\nERROR dispatch found {impl} {impl.exec_method(recv)} impl2 {impl2} required {propdef}"
				print "Pattern {callsite.mocallsite.pattern.rst}#{callsite.mocallsite.pattern.gp} {callsite.mocallsite.pattern.callees}"
				print "preexistence {callsite.mocallsite.expr_preexist} preexistence_origin {callsite.mocallsite.preexistence_origin}"
				print "Pattern.loaded_subclasses {callsite.mocallsite.pattern.rsc.loaded_subclasses} {callsite.mocallsite.pattern.rsc.get_position_methods(callsite.mocallsite.pattern.gp.intro_mclassdef.mclass)}"

				callsite.mocallsite.ast.dump_tree

				# abort
			end

			if impl isa StaticImplMethod then
				if not impl2 isa StaticImplMethod then
					print "impl {impl} impl2 {impl2} {callsite.mocallsite.can_be_static}"
					# print "Pattern {callsite.mocallsite.pattern.rst}#{callsite.mocallsite.pattern.gp} {callsite.mocallsite.pattern.callees}"
					# if callsite.mocallsite.concretes_receivers != null then
					# 	print "Concrete receivers {callsite.mocallsite.concretes_receivers.as(not null)}"
					# 	print "Concrete callees {callsite.mocallsite.concrete_callees}"
					# 	print "Concrete callees {callsite.mocallsite.concrete_callees.first.is_compiled}"
					# 	print "pattern.cuc {callsite.mocallsite.pattern.cuc} {callsite.mocallsite.pattern.can_be_static}"
					# end
					# print "Pattern.loaded_subclasses {callsite.mocallsite.pattern.rsc.loaded_subclasses}\n\n"
				end
			else if impl isa SSTImpl then
				if not impl2 isa SSTImpl then
					print "\n\nimpl {impl} impl2 {impl2}"
					# print "monomorph site = {callsite.mocallsite.is_monomorph}, self site {callsite.mocallsite.to_s}"
					# print "Pattern {callsite.mocallsite.pattern.rsc}#{callsite.mocallsite.pattern.gp} {callsite.mocallsite.pattern.callees} cuc {callsite.mocallsite.pattern.cuc}"
					if callsite.mocallsite.concretes_receivers != null then
						print "Concrete receivers {callsite.mocallsite.concretes_receivers.as(not null)} monomorph {callsite.mocallsite.is_monomorph}"
						print "Concrete callees {callsite.mocallsite.concrete_callees} loaded ? {callsite.mocallsite.concretes_receivers.first.loaded}"
					end
					# print "Pattern.loaded_subclasses {callsite.mocallsite.pattern.rsc.loaded_subclasses}"
				end
			else if impl isa PHImpl then
				if not impl2 isa PHImpl then
					print "impl {impl} impl2 {impl2}"
					# print "monomorph site = {callsite.mocallsite.is_monomorph}, self site {callsite.mocallsite.to_s}"
					# print "Pattern {callsite.mocallsite.pattern.rsc}#{callsite.mocallsite.pattern.gp} {callsite.mocallsite.pattern.callees}"
					# print "Concrete receivers {callsite.mocallsite.concretes_receivers.as(not null)} preexistence {callsite.mocallsite.expr_preexist} preexistence_origin {callsite.mocallsite.preexistence_origin}"
					# print "Pattern.loaded_subclasses {callsite.mocallsite.pattern.rsc.loaded_subclasses} {callsite.mocallsite.pattern.rsc.get_position_methods(callsite.mocallsite.pattern.gp.intro_mclassdef.mclass)}"
				end
			end

			return self.call(impl.exec_method(recv), args)
		else
			# TODO: handle this
			# print "CallSite without MOCallSite {callsite} {callsite.mproperty}"
		end

		return self.call(propdef, args)
	end

	redef fun read_variable(v: Variable): Instance
	do
		debug_variables(v)
		return super
	end

	# Assign the value of the `Variable` in an environment
	redef fun write_variable(v: Variable, value: Instance)
	do
		debug_variables(v)
		super
	end

	# Verify that a Variable object has its corresponding MOVar
	fun debug_variables(v: Variable)
	do
		if sys.debug_mode then
			if v.movar == null then
				debug_file.write("ERROR {v} with dependences {v.dep_exprs} does not have a MOVAR\n")
			end
		end
	end

	# TODO: put some parts of this in pattern classes
	redef fun load_class_indirect(mclass)
	do
		if mclass.abstract_loaded then return

		super(mclass)

		mclass.update_self_sites

		# Update Patterns and sites

		# Some method patterns can be static and become in SST
		for pattern in mclass.sites_patterns do
			# First, we need to update callees for these patterns
			if pattern isa MOCallSitePattern then
				var lp_rsc = pattern.gp.lookup_first_definition(mainmodule, pattern.rsc.intro.bound_mtype)
				pattern.add_lp(lp_rsc)
			end

			pattern.reinit_impl
			pattern.compute_impl

			# Update if any mosites of this pattern with a NullImpl
			for mosite in pattern.sites do
				mosite.reinit_impl
				mosite.get_impl(vm)
			end

			if pattern.rsc == mclass then
				# Reinit sites which had `mclass` as their rsc
				for mosite in pattern.sites do
					mosite.reinit_impl
					mosite.get_impl(vm)
				end
			end
		end

		# If `mclass` was a target of a subtyping test, go in these patterns and
		# recompute them because they were static
		for pattern in mclass.subtype_target_patterns do
			if pattern.get_impl(vm) isa StaticImpl then
				pattern.reinit_impl
				pattern.compute_impl
			end

			for mosite in pattern.sites do
				if mosite.get_impl(vm) isa StaticImpl then
					mosite.reinit_impl
					mosite.get_impl(vm)
				end
			end
		end
	end

	redef fun load_class(mclass)
	do
		if mclass.loaded then return

		super(mclass)

		for parent in mclass.in_hierarchy(mainmodule).direct_greaters do propagate_loading(parent)

		# for pattern in mclass.sites_patterns do
		# 	pattern.reinit_impl
		# 	pattern.get_impl(vm)

		# 	for site in pattern.sites do
		# 		site.reinit_impl
		# 		site.get_impl(vm)
		# 	end
		# end

		# Recompute the implementation of sites with `mclass` as a concrete
		for site in mclass.concrete_sites do
			site.reinit_impl
			site.get_impl(self)
		end
	end

	fun propagate_loading(mclass: MClass)
	do
		for parent in mclass.in_hierarchy(mainmodule).direct_greaters do propagate_loading(parent)

		mclass.update_self_sites
	end
end

redef class AAttrFormExpr
	# Position of the attribute in attribute table
	#
	# The relative position of this attribute if perfect hashing is used,
	# The absolute position of this attribute if SST is used
	var offset: Int is noinit

	# Indicate the status of the optimization for this node
	#
	# 0: default value
	# 1: SST (direct access) can be used
	# 2: PH (multiple inheritance implementation) must be used
	var status: Int = 0

	# Identifier of the class which introduced the attribute
	var id: Int is noinit

	# Optimize this attribute access
	# * `mproperty` The attribute which is accessed
	# * `recv` The receiver (The object) of the access
	protected fun optimize(mproperty: MAttribute, recv: MutableInstance)
	do
		var position = recv.mtype.as(MClassType).mclass.get_position_attributes(mproperty.intro_mclassdef.mclass)
		if position > 0 then
			# if this attribute class has an unique position for this receiver, then use direct access
			offset = position + mproperty.offset
			status = 1
		else
			# Otherwise, perfect hashing must be used
			id = mproperty.intro_mclassdef.mclass.vtable.as(not null).id
			offset = mproperty.offset
			status = 2
		end
	end

	# Debug attribute accesses
	fun debug_attr_model
	do
		if sys.debug_mode then
			if mo_entity == null then
				dump_tree

				print "\n\n"
				parent.dump_tree
				debug_file.write("ERROR {self} does not have a mo_entity\n")
			end
		end
	end
end

redef class AAttrExpr
	redef fun expr(v)
	do
		assert v isa VirtualMachine

		debug_attr_model

		var recv = v.expr(self.n_expr)
		if recv == null then return null
		if recv.mtype isa MNullType then fatal(v, "Receiver is null")
		var mproperty = self.mproperty.as(not null)

		assert recv isa MutableInstance

		if status == 0 then optimize(mproperty, recv)

		var i: Instance
		if status == 1 then
			# SST
			i = v.read_attribute_sst(recv.internal_attributes, offset)
		else
			# PH
			i = v.read_attribute_ph(recv.internal_attributes, recv.vtable.as(not null).internal_vtable, recv.vtable.as(not null).mask, id, offset)
		end

		# If we get a `MInit` value, throw an error
		if i == v.initialization_value then
			v.fatal("Uninitialized attribute {mproperty.name}")
			abort
		end

		# Test with new mechanisms
		if mo_entity != null then
			var impl = mo_entity.as(MOReadSite).get_impl(vm)

			var instance = impl.exec_attribute_read(recv)

			if instance != i then
				print "ERROR attribute read instance = {instance}, i = {i}"
			end
		else
			print "mo_entity null in {self}"
		end

		#TODO : we need recompilations here
		status = 0

		return i
	end
end

redef class AAttrAssignExpr
	redef fun stmt(v)
	do
		assert v isa VirtualMachine

		debug_attr_model

		var recv = v.expr(self.n_expr)
		if recv == null then return
		if recv.mtype isa MNullType then fatal(v, "Receiver is null")
		var i = v.expr(self.n_value)
		if i == null then return
		var mproperty = self.mproperty.as(not null)

		assert recv isa MutableInstance
		# if status == 0 then optimize(mproperty, recv)

		# if status == 1 then
		# 	v.write_attribute_sst(recv.internal_attributes, offset, i)
		# else
		# 	v.write_attribute_ph(recv.internal_attributes, recv.vtable.as(not null).internal_vtable,
		# 			recv.vtable.as(not null).mask, id, offset, i)
		# end

		# Test with new mechanisms
		if mo_entity != null then
			var impl = mo_entity.as(MOWriteSite).get_impl(vm)

			impl.exec_attribute_write(recv, i)
		else
			print "mo_entity null in {self}"
		end

		#TODO : we need recompilations here
		# status = 0
	end
end

redef class ASendExpr
	redef fun expr(v)
	do
		if sys.debug_mode then
			if mo_entity == null then
				dump_tree
				print "\n\n"
				parent.dump_tree
				debug_file.write("ERROR {self} does not have a mo_entity\n")
			end
		end

		return super
	end
end

# Add informations to optimize some method calls
redef class CallSite
	# Position of the method in virtual table
	#
	# The relative position of this MMethod if perfect hashing is used,
	# The absolute position of this MMethod if SST is used
	var offset: Int is noinit

	# Indicate the status of the optimization for this node
	#
	# 0: default value
	# 1: SST (direct access) can be used
	# 2: PH (multiple inheritance implementation) must be used
	var status: Int = 0

	# Identifier of the class which introduced the MMethod
	var id: Int is noinit

	# Optimize a method dispatch,
	# If this method is always at the same position in virtual table, we can use direct access,
	# Otherwise we must use perfect hashing
	fun optimize(recv: Instance)
	do
		var position = recv.mtype.as(MClassType).mclass.get_position_methods(mproperty.intro_mclassdef.mclass)
		if position > 0 then
			offset = position + mproperty.offset
			status = 1
		else
			offset = mproperty.offset
			status = 2
		end
		id = mproperty.intro_mclassdef.mclass.vtable.as(not null).id
	end
end

redef class ASubtypeExpr
	# The common part of the subtyping test, test nullables, nulls etc.
	# If the subtyping test can be answered with that returns the result, else `null`
	fun subtype_commons(sub: MType, sup: MType): nullable Bool
	do
		if sub == sup then return true

		var anchor = vm.frame.arguments.first.mtype.as(MClassType)

		# `sub` or `sup` are formal or virtual types, resolve them to concrete types
		if sub isa MFormalType then
			sub = sub.resolve_for(anchor.mclass.mclass_type, anchor, vm.mainmodule, false)
		end
		if sup isa MFormalType then
			sup = sup.resolve_for(anchor.mclass.mclass_type, anchor, vm.mainmodule, false)
		end

		var sup_accept_null = false
		if sup isa MNullableType then
			sup_accept_null = true
			sup = sup.mtype
		else if sup isa MNullType then
			sup_accept_null = true
		end

		# Can `sub` provides null or not?
		# Thus we can match with `sup_accept_null`
		# Also discard the nullable marker if it exists
		if sub isa MNullableType then
			if not sup_accept_null then return false
			sub = sub.mtype
		else if sub isa MNullType then
			return sup_accept_null
		end
		# Now the case of direct null and nullable is over

		if sub isa MFormalType then
			sub = sub.anchor_to(vm.mainmodule, anchor)
			# Manage the second layer of null/nullable
			if sub isa MNullableType then
				if not sup_accept_null then return false
				sub = sub.mtype
			else if sub isa MNullType then
				return sup_accept_null
			end
		end

		# `sup` accepts only null
		if sup isa MNullType then return false

		# All cases have been checked, now the test is class against class
		return null
	end
end

redef class AIsaExpr
	# Identifier of the target class type
	var id: Int is noinit

	# If the Cohen test is used, the position of the target id in vtable
	var position: Int is noinit

	# Indicate the status of the optimization for this node
	#
	# 0 : the default value
	# 1 : this test can be implemented with direct access
	# 2 : this test must be implemented with perfect hashing
	var status: Int = 0

	redef fun expr(v)
	do
		assert v isa VirtualMachine

		if sys.debug_mode then
			if mo_entity == null then
				debug_file.write("ERROR {self} does not have a mo_entity\n")
			end
		end

		var recv = v.expr(self.n_expr)
		if recv == null then return null

		optimize(v, recv.mtype, self.cast_type.as(not null))
		var mtype = v.unanchor_type(self.cast_type.as(not null))

		# If this test can be optimized, directly call appropriate subtyping methods
		var subtype_res
		if status == 1 and recv.mtype isa MClassType then
			# Direct access
			subtype_res = v.inter_is_subtype_sst(id, position, recv.mtype.as(MClassType).mclass.vtable.as(not null).internal_vtable)
		else if status == 2 and recv.mtype isa MClassType then
			# Perfect hashing
			subtype_res = v.inter_is_subtype_ph(id, recv.vtable.as(not null).mask, recv.mtype.as(MClassType).mclass.vtable.as(not null).internal_vtable)
		else
			# Use the slow path (default)
			subtype_res = v.is_subtype(recv.mtype, mtype)
		end

		if mo_entity != null then
			var impl = mo_entity.as(MOSubtypeSite).get_impl(vm)

			var res_mo = subtype_commons(recv.mtype, mtype)
			if res_mo != null then
				if res_mo != subtype_res then
					print "ERROR"
				end

				return v.bool_instance(subtype_res)
			end

			if impl.exec_subtype(recv) != subtype_res then
				print "ERROR AIsaExpr {impl} {impl.exec_subtype(recv)} {subtype_res} recv.mtype {recv.mtype} target_type {mtype}"
				print "Pattern.rst {mo_entity.as(MOSubtypeSite).pattern.rst} -> {mo_entity.as(MOSubtypeSite).pattern.target_mclass}"
				print "Exec recv {recv.mtype} target {mtype}"

				abort
			end
		end

		return v.bool_instance(subtype_res)
	end

	# Optimize a `AIsaExpr`
	# `source` the source type of the expression
	# `target` the target type of the subtyping test
	private fun optimize(v: VirtualMachine, source: MType, target: MType)
	do
		# If the source class and target class are not classic classes (non-generics) then return
		if not source isa MClassType or not target isa MClassType or target isa MGenericType then
			return
		end

		if not target.mclass.abstract_loaded then return

		# If the value is positive, the target class has an invariant position in source's structures
		var value = source.mclass.get_position_methods(target.mclass)

		if value > 0 then
			# `value - 2` is the position of the target identifier in source vtable
			position = value - 2
			status = 1
		else
			# We use perfect hashing
			status = 2
		end
		id = target.mclass.vtable.as(not null).id
	end
end

redef class AAsCastExpr
	# Identifier of the target class type
	var id: Int is noinit

	# If the Cohen test is used, the position of the target id in vtable
	var position: Int is noinit

	# Indicate the status of the optimization for this node
	#
	# 0 : the default value
	# 1 : this test can be implemented with direct access
	# 2 : this test must be implemented with perfect hashing
	var status: Int = 0

	redef fun expr(v)
	do
		assert v isa VirtualMachine

		if sys.debug_mode then
			if mo_entity == null then
				debug_file.write("ERROR {self} does not have a mo_entity\n")
			end
		end

		var recv = v.expr(self.n_expr)
		if recv == null then return null

		optimize(v, recv.mtype, self.mtype.as(not null))

		var mtype = self.mtype.as(not null)
		var amtype = v.unanchor_type(mtype)

		var res: Bool
		if status == 1 and recv.mtype isa MClassType then
			# Direct access
			res = v.inter_is_subtype_sst(id, position, recv.mtype.as(MClassType).mclass.vtable.as(not null).internal_vtable)
		else if status == 2 and recv.mtype isa MClassType then
			# Perfect hashing
			res = v.inter_is_subtype_ph(id, recv.vtable.as(not null).mask, recv.mtype.as(MClassType).mclass.vtable.as(not null).internal_vtable)
		else
			# Use the slow path (default)
			res = v.is_subtype(recv.mtype, amtype)
		end

		if mo_entity != null then
			var impl = mo_entity.as(MOSubtypeSite).get_impl(vm)

			var res_mo = subtype_commons(recv.mtype, mtype)
			if res_mo != null then
				if res_mo != res then
					print "ERROR"
					abort
				end

				return recv
			end

			if impl.exec_subtype(recv) != res then
				print "ERROR AAsCastExpr {impl} {impl.exec_subtype(recv)} {res} recv.mtype {recv.mtype} target_type {mtype}"
				print "Pattern.rst {mo_entity.as(MOSubtypeSite).pattern.rst} -> {mo_entity.as(MOSubtypeSite).pattern.target_mclass}"
				print "Exec recv {recv.mtype} target {mtype}"

				abort
			end
		end

		if not res then
			fatal(v, "Cast failed. Expected `{amtype}`, got `{recv.mtype}`")
		end
		return recv
	end

	# Optimize a `AAsCastExpr`
	# * `source` the source type of the expression
	# * `target` the target type of the subtyping test
	private fun optimize(v: VirtualMachine, source: MType, target: MType)
	do
		# If the source class and target class are not classic classes (non-generics) then return
		if not source isa MClassType or not target isa MClassType or target isa MGenericType then
			return
		end

		if not target.mclass.loaded then return

		# If the value is positive, the target class has an invariant position in source's structures
		var value = source.mclass.get_position_methods(target.mclass)

		if value > 0 then
			# `value - 2` is the position of the target identifier in source vtable
			position = value - 2
			status = 1
		else
			# We use perfect hashing
			status = 2
		end
		id = target.mclass.vtable.as(not null).id
	end
end

redef class MPropDef
	redef fun compile_mo
	do
		super

		for site in self.mosites do site.get_impl(vm)
	end
end

redef class MClass
	# This method is called when `current_class` class is moved in virtual table of `self`
	# *`offset` The offset of block of methods of `current_class` in `self`
	redef fun moved_class_methods(vm, current_class, offset)
	do
		super

		for pic_pattern in current_class.pic_patterns do
			# The pic_class has several positions in the class hierarchy,
			# the PICPattern implementation became perfect hashing
			pic_pattern.propagate_ph_impl
		end
	end

	# This method is called when `current_class` class is moved in virtual table of `self`
	# *`offset` The offset of block of methods of `current_class` in `self`
	redef fun moved_class_attributes(vm, current_class, offset)
	do
		super

		for pic_pattern in current_class.pic_patterns do
			# The pic_class has several positions in the class hierarchy,
			# the PICPattern implementation became perfect hashing
			pic_pattern.propagate_ph_impl
		end
	end
end

redef class PICPattern
	# Implementation of the PICPattern
	var impl: nullable Implementation = null is writable

	# Assign `null` to `impl`
	# NOTE: This method must be use to set to null an Implementation before recompute it
	# This method can be redefined to count recompilations in the vm
	fun reinit_impl
	do
		impl = null
	end

	# Compute an appropriate Implementation based on the positions of recv_class and pic_class
	fun get_impl: Implementation
	do
		if impl == null then compute_impl
		return impl.as(not null)
	end

	# Compute an Implementation for self and set attribute `impl`
	private fun compute_impl
	do
		# If the pic is the root of the hierarchy
		if pic_class.is_instance_of_object(vm) then
			set_sst_impl(false)
			return
		end

		# If the recv_class and pic_class are loaded we can compute an implementation
		if recv_class.abstract_loaded and pic_class.abstract_loaded then
			# If the PIC is always at the same position in all loaded subclasses of pic
			if pic_pos_unique then
				# In all loaded subclasses of recv_class, the pic block is at the same position,
				# use sst mutable implementation
				set_sst_impl(true)
			else
				# The pic has several position in subclasses of recv_class,
				# we must use a perfect hashing non-mutable implementation
				set_ph_impl(false, pic_class.vtable.id)
			end
		else
			# The rst is not loaded but the pic is,
			# we can compute the implementation with pic's informations
			if pic_class.abstract_loaded then
				# By default, use perfect hashing
				set_ph_impl(false, pic_class.vtable.id)
			else
				# The RST and the PIC are not loaded, make a null implementation by default
				set_null_impl
			end
		end
	end

	# Set a single-subtyping implementation
	# *`mutable` Indicate if the implementation can change in the future
	fun set_sst_impl(mutable: Bool)
	do
		var pos_cls = get_block_position

		impl = new SSTImpl(self, mutable, pos_cls)
	end

	# Set a perfect hashing implementation
	# *`mutable` Indicate if the implementation can change in the future
	# *`id` The target identifier
	fun set_ph_impl(mutable: Bool, id: Int)
	do
		impl = new PHImpl(self, mutable, get_block_position, id)
	end

	# Set a null Implementation, i.e. the pic is not loaded
	fun set_null_impl
	do
		# This implementation is temporary and will be replaced if the corresponding class is loaded
		impl = new NullImpl(self, true, 0, pic_class)
	end

	# The PICPattern implementation became a perfect hashing implementation with a class loading
	# This method propagates the change to its patterns
	fun propagate_ph_impl
	do
		if impl != null and impl isa PHImpl then return

		# Replace the old implementation
		reinit_impl
		impl = new PHImpl(self, false, get_block_position, pic_class.vtable.id)

		# Propagate this change in patterns
		for pattern in patterns do
			pattern.as(MOSitePattern).propagate_ph_impl
		end
	end

	# Tell if the pic is at a unique position on whole class hierarchy
	fun pic_pos_unique: Bool
	do
		return get_pic_position > 0
	end

	# Return the position of the PIC block in recv class
	fun get_block_position: Int is abstract

	# Return the position of the pic (neg. value if pic is at multiple positions)
	fun get_pic_position: Int is abstract
end

redef class MethodPICPattern
	redef fun get_block_position: Int
	do
		return recv_class.get_position_methods(pic_class)
	end

	redef fun get_pic_position: Int
	do
		if pic_class.position_methods > 0 then return pic_class.position_methods

		# See if loaded subclasses of the RSC have a unique position
		return recv_class.get_position_methods(pic_class)
	end
end

redef class AttributePICPattern
	redef fun get_block_position: Int
	do
		return recv_class.get_position_attributes(pic_class)
	end

	redef fun get_pic_position: Int
	do
		if pic_class.position_attributes > 0 then return pic_class.position_attributes

		# See if loaded subclasses of the RSC have a unique position
		return recv_class.get_position_attributes(pic_class)
	end
end

redef abstract class MOSitePattern
	# Implementation of the pattern (used if site has not concrete receivers list)
	var impl: nullable Implementation is writable, noinit

	# Assign `null` to `impl`
	# NOTE: This method must be use to set to null an Implementation before recompute it
	# This method can be redefined to count recompilations in the vm
	fun reinit_impl
	do
		impl = null
	end

	# Change the Implementation to a PHImpl
	fun propagate_ph_impl
	do
		if impl != null and impl isa PHImpl then return

		reinit_impl

		set_ph_impl(vm, false, get_pic(vm).vtable.id)

		for site in sites do
			site.propagate_ph_impl
		end
	end

	# Get implementation, compute it if not exists
	fun get_impl(vm: VirtualMachine): Implementation
	do
		if impl == null then compute_impl
		return impl.as(not null)
	end

	# Compute the implementation of this pattern and set attribute `impl`
	private fun compute_impl is abstract

	# Get the relative offset of the "property" (gp for MOPropPattern, method block offset for MOSubtypeSitePattern)
	private fun get_offset(vm: VirtualMachine): Int is abstract

	# Return `true` if the pattern can be static
	# False by default
	fun can_be_static: Bool
	do
		return false
	end

	# Set a static implementation
	# `mutable` If true, the implementation can change in the future
	fun set_static_impl(mutable: Bool) is abstract

	# Set a sst impl
	fun set_sst_impl(vm: VirtualMachine, mutable: Bool)
	do
		var offset = get_offset(vm)
		var pos_cls = get_block_position

		impl = new SSTImpl(self, mutable, pos_cls + offset)
	end

	# Set a perfect hashing implementation
	# *`mutable` Indicate if the implementation can change in the future
	# *`id` The target identifier
	fun set_ph_impl(vm: VirtualMachine, mutable: Bool, id: Int)
	do
		var offset = get_offset(vm)

		impl = new PHImpl(self, mutable, offset, id)
	end

	# Return true if the pic is at a unique position on the whole class hierarchy
	fun pic_pos_unique: Bool
	do
		return get_pic(vm).position_attributes > 0
	end

	# Return the offset of the introduction property of the class
	fun get_block_position: Int is abstract

	# Return the position of the pic for this rsc (neg. value if pic is at multiple positions)
	fun get_pic_position: Int is abstract
end

redef class MOAttrPattern
	redef fun compute_impl
	do
		if rsc.abstract_loaded then
			if pic_pos_unique then
				set_sst_impl(vm, true)
			else
				set_ph_impl(vm, true, get_pic(vm).vtable.id)
			end
		else
			if get_pic(vm).is_instance_of_object(vm) then
				set_sst_impl(vm, false)
				return
			end

			# The rst is not loaded but the pic is,
			# we can compute the implementation with pic's informations
			if get_pic(vm).abstract_loaded then
				# By default, use perfect hashing
				set_ph_impl(vm, false, get_pic(vm).vtable.id)
			else
				# The RST and the PIC are not loaded, make a null implementation by default
				impl = new NullImpl(self, true, 0, get_pic(vm))
			end
		end
	end

	redef fun get_block_position
	do
		return rsc.get_position_attributes(get_pic(vm))
	end

 	redef fun get_pic_position
 	do
 		return rsc.get_position_attributes(get_pic(vm))
 	end

	redef fun set_static_impl(mutable) do abort

	redef fun set_sst_impl(vm: VirtualMachine, mutable: Bool)
	do
		var offset = get_offset(vm)
		var pos_cls = get_block_position
		impl = new SSTImpl(self, mutable, pos_cls + offset)
	end
end

redef class MOCallSitePattern
	redef fun set_static_impl(mutable)
	do
		if rsc.is_final then
			impl = new StaticImplMethod(self, mutable, gp.lookup_first_definition(sys.vm.mainmodule, rsc.intro.bound_mtype))
		else
			impl = new StaticImplMethod(self, mutable, callees.first)
		end
	end

	redef fun can_be_static
	do
		# If the rsc is a final class
		if rsc.is_final and rsc.loaded then return true

		return callees.length == 1 and cuc == 0
	end

	redef fun compute_impl
	do
		if can_be_static then
			set_static_impl(true)
			return
		end

		if rsc.abstract_loaded then
			if can_be_static then
				set_static_impl(true)
			else if pic_pos_unique then
				set_sst_impl(vm, true)
			else
				set_ph_impl(vm, true, get_pic(vm).vtable.id)
			end
		else
			if get_pic(vm).is_instance_of_object(vm) then
				set_sst_impl(vm, false)
				return
			end

			# The rst is not loaded but the pic is,
			# we can compute the implementation with pic's informations
			if get_pic(vm).abstract_loaded then
				# By default, use perfect hashing
				set_ph_impl(vm, false, get_pic(vm).vtable.id)
			else
				# The RST and the PIC are not loaded, make a null implementation by default
				impl = new NullImpl(self, true, 0, get_pic(vm))
			end
		end
	end

	redef fun get_block_position: Int
	do
		return rsc.get_position_methods(get_pic(vm))
	end

	redef fun get_pic_position: Int
	do
		# If the pic is at the same position for all loaded subclasses
		if get_pic(vm).position_methods > 0 then
			return get_pic(vm).position_methods
		else
			# The pic has not the same position for all loaded subclasses,
			# see if the position is constant for subclasses of the rst
			return get_pic(vm).position_methods
		end
	end

	redef fun add_lp(lp)
	do
		var reset = not callees.has(lp)

		super(lp)
		if reset then
			if impl != null and impl.as(not null).is_mutable then
				reinit_impl
			end

			for site in sites do
				if site.impl != null and site.impl.as(not null).is_mutable then
					site.reinit_impl
				end
			end
		end
	end

	redef fun decrement_cuc
	do
		super

		# Now, recompute the implementation of this pattern and its sites
		reinit_impl
		compute_impl

		for site in sites do
			# TODO: recompute only sites with a mutable implementation
			site.reinit_impl
			site.get_impl(vm)
		end
	end
end

redef class MOSubtypeSitePattern
	redef fun get_offset(vm) do return get_pic(vm).color

	redef fun compute_impl
	do
		if rsc.abstract_loaded and get_pic(vm).abstract_loaded then
			if can_be_static then
				set_static_impl(true)
			else if can_be_sst then
				set_sst_impl(vm, true)
			else
				# By default, use perfect hashing
				set_ph_impl(vm, false, get_pic(vm).vtable.id)
			end
		else
			if can_be_static then
				set_static_impl(true)
			else
				# By default, use perfect hashing
				set_ph_impl(vm, false, get_pic(vm).vtable.id)
			end
		end
	end

	# Indicates if self can be implemented with sst,
	# i.e. if for all subclasses of the rst, the pic class is always at the same position
	fun can_be_sst: Bool
	do
		# The set of loaded classes which are subtype of both the source and the target of the test
		var classes = new List[MClass]

		for mclass in rsc.loaded_subclasses do
			if vm.is_subclass(mclass, target_mclass) then
				classes.add(mclass)
			end
		end

		if classes.is_empty then return false
		# `classes` now contains all classes that can actually be tested against the target

		# The position of the target in the first subclass of the rst
		var first_position = classes.first.get_position_methods(target_mclass)

		# Go check if all other subclasses have the same position than the first one
		for mclass in classes do
			var pos = mclass.get_position_methods(target_mclass)

			# If one position differs then the cast must be implemented with perfect hashing
			if pos != first_position then return false
		end

		return true
	end

	redef fun can_be_static
	do
		# If the rst of the cast, is not a MClassType, we can not optimize
		if not rst isa MClassType then return false

		# If the target is not loaded, the cast will always fail
		if not target_mclass.abstract_loaded then return true

		# If the rsc is a subclass of the target, then the test will always be true
		if vm.is_subclass(rsc, target_mclass) then return true

		return false
	end

	redef fun get_block_position: Int
	do
		return rsc.get_position_methods(get_pic(vm))
	end

	redef fun set_static_impl(mutable)
	do
		# The result of the subtyping test
		var res: Bool = false

		# If the target is not loaded, the test will always fail
		if not target_mclass.abstract_loaded then res = false

		# If the rsc is a subclass of the target, then the test will always be true
		if vm.is_subclass(rsc, target_mclass) then res = true

		impl = new StaticImplSubtype(self, false, res)
	end

	redef fun set_sst_impl(vm: VirtualMachine, mutable: Bool)
	do
		var offset = get_offset(vm)
		var pos_cls = get_block_position
		impl = new SSTImplSubtype(self, mutable, offset, get_pic(vm).vtable.id)
	end
end

redef class MOAsNotNullPattern
	redef fun get_offset(vm) do return 0

	redef fun compute_impl
	do
		# TODO
		if rsc.abstract_loaded then
			if can_be_static then
				set_static_impl(true)
			else
				set_sst_impl(vm, true)
			end
		else
			# The rst is not loaded but the pic is,
			# we can compute the implementation with pic's informations
			if get_pic(vm).abstract_loaded then
				var pos_cls = get_block_position
				if get_pic(vm).is_instance_of_object(vm) then
					set_sst_impl(vm, false)
				else if can_be_static then
					set_static_impl(true)
				else
					# By default, use perfect hashing
					set_ph_impl(vm, false, get_pic(vm).vtable.id)
				end
			else
				# The RST and the PIC are not loaded, make a null implementation by default
				impl = new NullImpl(self, true, 0, get_pic(vm))
			end
		end
	end

	redef fun get_block_position: Int
	do
		return rsc.get_position_methods(get_pic(vm))
	end

	redef fun set_static_impl(mutable)
	do
		impl = new StaticImplSubtype(self, false, true)
	end

	redef fun can_be_static
	do
		return false
	end
end

redef abstract class MOPropSitePattern
	redef fun get_offset(vm) do return gp.offset
end

redef abstract class MOSite
	# Implementation of the site (null if can't determine concretes receivers)
	# get_impl must be used to read this value
	var impl: nullable Implementation is writable

	# Assign `null` to `impl`
	# NOTE: This method must be use to set to null an Implementation before recompute it
	# This method can be redefined to count recompilations in the vm
	fun reinit_impl
	do
		impl = null
	end

	# Change the Implementation to ph_impl if the site has no concrete types
	fun propagate_ph_impl
	do
		compute_concretes_site

		if impl != null then reinit_impl

		if concretes_receivers == null then
			set_ph_impl(vm, false)
		else
			compute_impl_concretes(vm)
		end
	end

	# Get the implementation of the site, according to preexist value
	fun get_impl(vm: VirtualMachine): Implementation
	do
		if impl != null then return impl.as(not null)

		return compute_impl
	end

	# Compute an Implementation for self site and assign `impl`
	# Return the Implementation of the Site
	fun compute_impl: Implementation
	do
		monomorphic_analysis
		compute_concretes_site

		if not get_pic(vm).abstract_loaded then
			set_null_impl
		else
			if concretes_receivers == null and not is_monomorph then
				# Recopy the implementation of the pattern
				var pattern_impl = pattern.get_impl(vm)
				if pattern_impl isa StaticImpl then
					set_static_impl(vm, true)
				else if pattern_impl isa SSTImpl then
					set_sst_impl(vm, true)
				else
					set_ph_impl(vm, true)
				end
			else
				compute_impl_concretes(vm)
			end
		end

		impl.mo_entity = self

		return impl.as(not null)
	end

	# Compute the implementation with rst/pic, and concretes if any
	# TODO: finish to comment the code
	fun compute_impl_concretes(vm: VirtualMachine)
	do
		# Static
		if can_be_static then
			set_static_impl(vm, true)
			return
		end

		if is_monomorph then
			# Ensure that the concrete type of the site is loaded
			if concretes_receivers.first.abstract_loaded then
				# callsite and casts are implemented in static
				if can_be_static then
					set_static_impl(vm, false)
				else
					# Attributes are implemented in SST
					set_sst_impl(vm, false)
				end
				return
			end
		end

		# If the property is introduced in Object class, SST can be used
		if get_pic(vm).is_instance_of_object(vm) then
			set_sst_impl(vm, false)
			return
		end

		if not pattern.rsc.abstract_loaded then
			set_ph_impl(vm, true)
			return
		end

		var unique_pos_indicator = unique_pos_for_each_recv(vm)

		if unique_pos_indicator == 1 then
			# SST immutable because statically, it can't be more than these concrete receivers
			set_sst_impl(vm, false)
		else if unique_pos_indicator == -1 then
			# Some receiver classes are not loaded yet, so we use a mutable implementation
			set_ph_impl(vm, true)
		else
			set_ph_impl(vm, false)
		end
	end

	# Indicates if each concrete receiver has a unique method's position:
	# * -1: some classes are still unloaded
	# * 0: no unique position
	# * 1: unique position
	private fun unique_pos_for_each_recv(vm: VirtualMachine): Int
	do
		var position = -1

		# If the rsc does not have a unique position for its methods in all its loaded subclasses
		if pattern.rsc.position_methods < 0 then return 0

		if concretes_receivers != null then

			var current_pos = get_block_position(vm, concretes_receivers.first)
			for recv in concretes_receivers.as(not null) do
				if not recv.loaded then return -1

				if get_block_position(vm, recv) < 0 then
					return 0
				else if get_block_position(vm, recv) != current_pos then
					return 0
				end
			end

			return 1
		end

		return 0
	end

	# Return the position of the block of PIC class in the receiver static class
	private fun get_block_position(vm: VirtualMachine, recv: MClass): Int
	do
		return recv.get_position_methods(get_pic(vm))
	end

	# Return the pic
	# In case of the subtype test, the pic is the target class
	fun get_pic(vm: VirtualMachine): MClass is abstract

	# Return the offset of the "targeted property"
	# (eg. gp.offset for MOPropSite, a_class.color for MOSubtypeSite)
	private fun get_offset(vm: VirtualMachine): Int is abstract

	# Tell if the implementation can be static
	fun can_be_static: Bool
	do
		return pattern.can_be_static
	end

	# Set a static implementation
	fun set_static_impl(vm: VirtualMachine, mutable: Bool) is abstract

	# Set a sst implementation
	fun set_sst_impl(vm: VirtualMachine, mutable: Bool)
	do
		var offset = get_offset(vm)
		var pos_cls = get_block_position(vm, pattern.rsc)

		impl = new SSTImpl(self, mutable, pos_cls + offset)
	end

	# Set a ph implementation
	fun set_ph_impl(vm: VirtualMachine, mutable: Bool)
	do
		var offset = get_offset(vm)

		impl = new PHImpl(self, mutable, offset, get_pic(vm).vtable.id)
	end

	# Set a null implementation (eg. PIC null)
	fun set_null_impl
	do
		impl = new NullImpl(self, true, get_offset(sys.vm), get_pic(sys.vm))
	end

	# Compute and return the conservative implementation of this site
	# The conservative implementation is the Implementation that will never require recompiling the site
	fun conservative_implementation: Implementation
	do
		# SST for a property introduced in Object
		if get_pic(vm).is_instance_of_object(vm) then
			return new SSTImpl(self, false, get_block_position(vm, pattern.rsc) + get_offset(vm))
		else
			# By default, perfect hashing
			return new PHImpl(self, false, get_offset(vm), get_pic(vm).vtable.id)
		end
	end
end

redef class MOSubtypeSite
	redef fun get_offset(vm) do return get_pic(vm).color

	redef fun get_pic(vm) do return target.get_mclass(vm, lp).as(not null)

	# Compute an Implementation for self site and assign `impl`
	# Return the Implementation of the Site
	redef fun compute_impl: Implementation
	do
		monomorphic_analysis
		compute_concretes_site

		impl = pattern.get_impl(vm)
		impl.mo_entity = self

		#TODO: compute_impl_concretes
		return impl.as(not null)
	end

	redef fun set_static_impl(vm, mutable)
	do
		if not get_pic(vm).abstract_loaded then
			impl = new StaticImplSubtype(self, mutable, false)
		else
			var target_id = get_pic(vm).vtable.as(not null).id
			var source_vt = pattern.rsc.vtable.as(not null)
			var cast_value = vm.inter_is_subtype_ph(target_id, source_vt.mask, source_vt.internal_vtable)
			impl = new StaticImplSubtype(self, mutable, cast_value)
		end
	end

	redef fun conservative_implementation: Implementation
	do
		# Static for casts when the target type is final
		if target_mclass.is_final then
			return new StaticImplSubtype(self, false, true)
		else
			# Else we use the default computation of conservative implementation
			return super
		end
	end
end

redef class MOAsNotNullSite
	redef fun get_offset(vm) do return 0

	redef fun get_pic(vm) do return pattern.rsc

	redef fun set_static_impl(vm, mutable)
	do
		if not get_pic(vm).loaded then
			impl = new StaticImplSubtype(self, mutable, false)
		else
			var target_id = get_pic(vm).vtable.as(not null).id
			var source_vt = pattern.rsc.vtable.as(not null)
			var cast_value = vm.inter_is_subtype_ph(target_id, source_vt.mask, source_vt.internal_vtable)
			impl = new StaticImplSubtype(self, mutable, cast_value)
		end
	end
end

redef abstract class MOPropSite
	redef fun get_offset(vm) do return pattern.gp.offset

	redef fun get_pic(vm) do return pattern.gp.intro_mclassdef.mclass
end

redef abstract class MOAttrSite
	redef fun can_be_static do return false

	redef fun set_static_impl(vm, mutable) do abort

	redef fun get_block_position(vm, recv) do return recv.get_position_attributes(get_pic(vm))

	redef fun set_sst_impl(vm: VirtualMachine, mutable: Bool)
	do
		var offset = get_offset(vm)
		var pos_cls = get_block_position(vm, pattern.rsc)
		impl = new SSTImpl(self, mutable, pos_cls + offset)
	end
end

redef class MOCallSite
	redef fun set_static_impl(vm, mutable)
	do
		if pattern.callees.length == 1 then
			impl = new StaticImplMethod(self, mutable, pattern.callees.first)
		else
			impl = new StaticImplMethod(self, mutable, concrete_callees.first)
		end
	end

	redef fun can_be_static
	do
		# If the pattern can be static, return true
		if pattern.can_be_static then return true

		if not pattern.rsc.abstract_loaded then return false

		if is_monomorph then return true

		if concretes_receivers == null then
			return false
		else
			if concrete_callees.length == 1 then
				return true
			else
				return false
			end
		end
	end

	redef fun conservative_implementation: Implementation
	do
		# Static, when the concrete types of the receiver are known
		if concretes_receivers != null then
			var callees = concrete_callees

			if callees.length == 1 then
				return new StaticImplMethod(self, false, concrete_callees.first)
			end
		end

		return super
	end
end

# The superclass of implementations of object mechanisms
abstract class Implementation
	# The entity which contains self, can be a PICPattern, Pattern or Site
	# TODO: find a better solution to type this attribute
	var mo_entity: Object

	# Is the implementation mutable in the future ?
	var is_mutable: Bool

	# Execute an attribute access
	# *`recv` The receiver
	# Return the read value
	fun exec_attribute_read(recv: MutableInstance): Instance is abstract

	# Execute an attribute writing
	# *`recv` The receiver
	# *`value` The value to write
	fun exec_attribute_write(recv: MutableInstance, value: Instance) is abstract

	# Execute a method dispatch
	# *`recv` The receiver
	fun exec_method(recv: Instance): MMethodDef is abstract

	# Execute a subtyping test
	# *`recv` The receiver
	# Return the result of the test
	fun exec_subtype(recv: Instance): Bool is abstract
end

# A null implementation
class NullImpl
	super Implementation

	# The (global if SST, relative if PH) offset of the property
	var offset: Int

	# The PIC of the implementation (not loaded at compile-time)
	var pic: MClass

	# The method load the PIC (the class which introduced the property),
	# Then it creates a new PHImpl for this site and return it
	fun trampoline(recv: Instance): PHImpl
	do
		sys.vm.load_class(recv.mtype.as(MClassType).mclass)

		return new PHImpl(self, true, offset, pic.vtable.id)
	end
end

# Commons properties on object mecanism implementations (sst, ph)
abstract class ObjectImpl
	super Implementation

	# The (global if SST, relative if PH) offset of the property
	var offset: Int
end

# SST implementation
class SSTImpl
	super ObjectImpl

	redef fun exec_attribute_read(recv)
	do
		return sys.vm.read_attribute_sst(recv.internal_attributes, offset)
	end

	redef fun exec_attribute_write(recv, instance)
	do
		sys.vm.write_attribute_sst(recv.internal_attributes, offset, instance)
	end

	redef fun exec_method(recv)
	do
		return sys.vm.method_dispatch_sst(recv.vtable.internal_vtable, offset)
	end
end

class SSTImplSubtype
	super SSTImpl

	# The target identifier for subtyping test
	var id: Int

	redef fun exec_subtype(recv: Instance)
	do
		return vm.inter_is_subtype_sst(id, offset, recv.mtype.as(MClassType).mclass.vtable.as(not null).internal_vtable)
	end
end

# Perfect hashing implementation
class PHImpl
	super ObjectImpl

	# The target identifier of the subtyping-test or the class which introduced the GP
	var id: Int

	redef fun exec_attribute_read(recv)
	do
		return sys.vm.read_attribute_ph(recv.internal_attributes, recv.vtable.internal_vtable, recv.vtable.mask, id, offset)
	end

	redef fun exec_attribute_write(recv, value)
	do
		sys.vm.write_attribute_ph(recv.internal_attributes, recv.vtable.internal_vtable, recv.vtable.mask, id, offset, value)
	end

	redef fun exec_method(recv)
	do
		return sys.vm.method_dispatch_ph(recv.vtable.internal_vtable, recv.vtable.mask, id, offset)
	end

	redef fun exec_subtype(recv: Instance)
	do
		return vm.inter_is_subtype_ph(id, recv.vtable.as(not null).mask, recv.mtype.as(MClassType).mclass.vtable.as(not null).internal_vtable)
	end
end

# Common class for static implementation between subtypes, attr, meth.
abstract class StaticImpl
	super Implementation
end

# Static implementation (used only for method call)
class StaticImplMethod
	super StaticImpl

	# The called lp
	var lp: MPropDef

	redef fun exec_method(recv)
	do
		return lp.as(MMethodDef)
	end
end

# Static implementation (used only for subtype tests)
class StaticImplSubtype
	super StaticImpl

	# Is subtype ?
	var is_subtype: Bool

	redef fun exec_subtype(recv: Instance)
	do
		# Directly return the cached value
		return is_subtype
	end
end
