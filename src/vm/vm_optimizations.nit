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
		return self.call(propdef, args)
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
end

redef class AAttrExpr
	redef fun expr(v)
	do
		assert v isa VirtualMachine

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

		#TODO : we need recompilations here
		status = 0

		return i
	end
end

redef class AAttrAssignExpr
	redef fun stmt(v)
	do
		assert v isa VirtualMachine

		var recv = v.expr(self.n_expr)
		if recv == null then return
		if recv.mtype isa MNullType then fatal(v, "Receiver is null")
		var i = v.expr(self.n_value)
		if i == null then return
		var mproperty = self.mproperty.as(not null)

		assert recv isa MutableInstance
		if status == 0 then optimize(mproperty, recv)

		if status == 1 then
			v.write_attribute_sst(recv.internal_attributes, offset, i)
		else
			v.write_attribute_ph(recv.internal_attributes, recv.vtable.as(not null).internal_vtable,
					recv.vtable.as(not null).mask, id, offset, i)
		end

		#TODO : we need recompilations here
		status = 0
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

		var recv = v.expr(self.n_expr)
		if recv == null then return null

		optimize(v, recv.mtype, self.cast_type.as(not null))
		var mtype = v.unanchor_type(self.cast_type.as(not null))

		# If this test can be optimized, directly call appropriate subtyping methods
		if status == 1 and recv.mtype isa MClassType then
			# Direct access
			return v.bool_instance(v.inter_is_subtype_sst(id, position, recv.mtype.as(MClassType).mclass.vtable.as(not null).internal_vtable))
		else if status == 2 and recv.mtype isa MClassType then
			# Perfect hashing
			return v.bool_instance(v.inter_is_subtype_ph(id, recv.vtable.as(not null).mask, recv.mtype.as(MClassType).mclass.vtable.as(not null).internal_vtable))
		else
			# Use the slow path (default)
			return v.bool_instance(v.is_subtype(recv.mtype, mtype))
		end
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

# TODO: De-optimize the inlining if needed
redef class MPropDef
	redef fun compile_mo
	do
		super

		for site in self.mosites do site.get_impl(vm)
	end
end

redef abstract class MOSitePattern
	# Implementation of the pattern (used if site as not concerte receivers list)
	var impl: nullable Implementation is noinit

	# Get implementation, compute it if not exists
	fun get_impl(vm: VirtualMachine): Implementation
	do
		if impl == null then compute_impl(vm)
		return impl.as(not null)
	end

	# Compute the implementation
	fun compute_impl(vm: VirtualMachine)
	do
		if rsc.loaded then
			if pic_pos_unique(vm) then
				if can_be_static then
					set_static_impl(true)
				else
					set_sst_impl(vm, true)
				end
			else
				set_ph_impl(vm, true, get_pic(vm).vtable.id)
			end
		else
			var pos_cls = get_bloc_position(vm)

			if get_pic(vm).is_instance_of_object(vm) then
				set_sst_impl(vm, false)
			else if can_be_static then
				set_static_impl(true)
			else if pos_cls > 0 then
				set_sst_impl(vm, true)
			else
				set_ph_impl(vm, false, get_pic(vm).vtable.id)
			end
		end
	end

	# Get the relative offset of the "property" (gp for MOPropPattern, methodblock offset for MOSubtypeSitePattern)
	private fun get_offset(vm: VirtualMachine): Int is abstract

	# Get the pic
	fun get_pic(vm: VirtualMachine): MClass is abstract

	# True if the pattern can be static
	# False by default
	fun can_be_static: Bool do return false

	# Set a static implementation
	fun set_static_impl(mutable: Bool) is abstract

	# Set a sst impl
	fun set_sst_impl(vm: VirtualMachine, mutable: Bool)
	do
		var offset = get_offset(vm)
		var pos_cls = get_bloc_position(vm)

		impl = new SSTImpl(mutable, pos_cls + offset)
	end

	# Set a ph impl
	# *`mutable` Indicate if the implementation can change in the future
	# *`id` The target identifier
	fun set_ph_impl(vm: VirtualMachine, mutable: Bool, id: Int)
	do
		var offset = get_offset(vm)

		impl = new PHImpl(mutable, offset, id)
	end

	# Return the offset of the introduction property of the class
	# Redef in MOAttrPattern to use MClass:get_position_attribute instead of get_position_method
	private fun get_bloc_position(vm: VirtualMachine): Int do return rsc.get_position_methods(get_pic(vm))

	# Tell if the pic is at unique position on whole class hierarchy
	private fun pic_pos_unique(vm: VirtualMachine): Bool do return get_pic_position(vm) > 0

	# Return the position of the pic (neg. value if pic is at multiple positions)
	# Redef in MOAttrPattern to use position_attributes
	private fun get_pic_position(vm: VirtualMachine): Int do return get_pic(vm).position_methods
end

redef class MOSubtypeSitePattern
	redef fun get_offset(vm) do return get_pic(vm).color

	redef fun get_pic(vm) do return target.as(MClassType).mclass

	redef fun can_be_static
	do
		# If the target is not loaded, the cast will always fail
		if not target_mclass.abstract_loaded then return true

		# If rsc has only one loaded subclass, then true
		if rsc.single_loaded_subclass(target_mclass) then return true

		return false
	end

	redef fun set_static_impl(mutable)
	do
		impl = new StaticImplSubtype(false, true)
	end
end

redef class MOAsNotNullPattern
	redef fun get_offset(vm) do return 0

	redef fun get_pic(vm) do return rsc

	redef fun set_static_impl(mutable)
	do
		impl = new StaticImplSubtype(false, true)
	end

	redef fun can_be_static
	do
		return false
	end
end

redef abstract class MOPropSitePattern
	redef fun get_offset(vm) do return gp.offset

	redef fun get_pic(vm) do return gp.intro_mclassdef.mclass
end

redef class MOAttrPattern
	redef fun get_bloc_position(vm) do return rsc.get_position_attributes(get_pic(vm))

 	redef fun get_pic_position(vm) do return get_pic(vm).position_attributes

	redef fun set_static_impl(mutable) do abort
end

redef class MOCallSitePattern
	redef fun set_static_impl(mutable) do impl = new StaticImplProp(mutable, callees.first)

	redef fun can_be_static do return callees.length == 1

	redef fun add_lp(lp)
	do
		var reset = not callees.has(lp)

		super(lp)
		if reset then
			if impl != null and impl.as(not null).is_mutable then impl = null
			for site in sites do
				if site.impl != null and site.impl.as(not null).is_mutable then site.impl = null
			end
		end
	end
end

redef abstract class MOSite
	# Implementation of the site (null if can't determine concretes receivers)
	# get_impl must be used to read this value
	var impl: nullable Implementation is writable, noinit

	# Get the implementation of the site, according to preexist value
	fun get_impl(vm: VirtualMachine): Implementation
	do
		if impl != null then return impl.as(not null)

		if not get_pic(vm).abstract_loaded then
			set_null_impl
			return impl.as(not null)
		else if get_concretes == null then
			return pattern.get_impl(vm)
		else
			compute_impl_concretes(vm)
			return impl.as(not null)
		end
	end

	# Compute the implementation with rst/pic, and concretes if any
	# TODO: comment the code
	fun compute_impl_concretes(vm: VirtualMachine)
	do
		# Static
		if can_be_static then
			set_static_impl(vm, true)
			return
		end

		if not get_pic(vm).abstract_loaded then
			set_null_impl
			return
		end

		if not pattern.rsc.abstract_loaded then
			set_ph_impl(vm, true)
			return
		end

		# SST
		if get_pic(vm).is_instance_of_object(vm) then
			set_sst_impl(vm, false)
			return
		end

		var unique_pos_indicator = unique_pos_for_each_recv(vm)

		if unique_pos_indicator == 1 then
			# SST immutable because it can't be more than these concretes receivers statically
			set_sst_impl(vm, false)
		else if unique_pos_indicator == -1 then
			# Some receivers classes are not loaded yet, so we use a mutable implementation
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

		if get_concretes != null then
			for recv in get_concretes do
				if not recv.loaded then return -1

				var bloc_position = get_bloc_position(vm, recv)
				if bloc_position < 0 then
					bloc_position = - bloc_position
				end

				if position == -1 then
					position = bloc_position
				else
					if position != bloc_position then return -1
				end
			end

			return 1
		else
			# See in patterns
			if get_bloc_position(vm, pattern.rsc) > 0 then
				return 1
			else
				return 0
			end
		end
	end

	# Must return the position given by MClass:get_position_method
	# Must be redefined by MOAttrSite to use MClass::get_position_attribute
	private fun get_bloc_position(vm: VirtualMachine, recv: MClass): Int
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
		var pos_cls = get_bloc_position(vm, pattern.rsc)

		impl = new SSTImpl(mutable, pos_cls + offset)
	end

	# Set a ph implementation
	fun set_ph_impl(vm: VirtualMachine, mutable: Bool)
	do
		var offset = get_offset(vm)

		impl = new PHImpl(mutable, offset, get_pic(vm).vtable.id)
	end

	# Set a null implementation (eg. PIC null)
	fun set_null_impl
	do
		impl = new NullImpl(true, self, get_offset(sys.vm), get_pic(sys.vm))
	end

	fun clone: MOSite
	do
		print "NYI {self}"
		return self
	end
end

redef class MOSubtypeSite
	redef fun get_offset(vm) do return get_pic(vm).color

	redef fun get_pic(vm) do return target.get_mclass(vm, lp).as(not null)

	redef fun set_static_impl(vm, mutable)
	do
		if not get_pic(vm).loaded then
			impl = new StaticImplSubtype(mutable, false)
		else
			var target_id = get_pic(vm).vtable.as(not null).id
			var source_vt = pattern.rsc.vtable.as(not null)
			var cast_value = vm.inter_is_subtype_ph(target_id, source_vt.mask, source_vt.internal_vtable)
			impl = new StaticImplSubtype(mutable, cast_value)
		end
	end
end

redef class MOAsNotNullSite
	redef fun get_offset(vm) do return 0

	redef fun get_pic(vm) do return pattern.rsc

	redef fun set_static_impl(vm, mutable)
	do
		if not get_pic(vm).loaded then
			impl = new StaticImplSubtype(mutable, false)
		else
			var target_id = get_pic(vm).vtable.as(not null).id
			var source_vt = pattern.rsc.vtable.as(not null)
			var cast_value = vm.inter_is_subtype_ph(target_id, source_vt.mask, source_vt.internal_vtable)
			impl = new StaticImplSubtype(mutable, cast_value)
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

	redef fun get_bloc_position(vm, recv) do return recv.get_position_attributes(get_pic(vm))
end

redef class MOCallSite
	redef fun set_static_impl(vm, mutable)
	do
		if get_concretes == null then
			var propdef = pattern.gp.lookup_first_definition(sys.vm.mainmodule, pattern.rst)
			impl = new StaticImplProp(mutable, propdef)
		else
			impl = new StaticImplProp(mutable, concretes_callees.first)
		end
	end

	# Clone a MOSite
	redef fun clone: MOSite
	do
		var copy = new MOCallSite(ast, lp)
		copy.pattern = pattern

		if concretes_receivers != null then
			copy.concretes_receivers = new List[MClass]
			copy.concretes_receivers.add_all(concretes_receivers.as(not null))
		end

		return copy
	end

	redef fun can_be_static
	do
		# If the pattern can be static, return true
		if super then return true

		if get_concretes == null then
			return false
		else
			return concretes_callees.length == 1
		end
	end
end

redef class MOReadSite
	# Clone a MOSite
	redef fun clone: MOSite
	do
		var copy = new MOReadSite(ast, lp)
		copy.pattern = pattern

		if concretes_receivers != null then
			copy.concretes_receivers = new List[MClass]
			copy.concretes_receivers.add_all(concretes_receivers.as(not null))
		end

		return copy
	end
end

# The superclass of implementations of object mechanisms
abstract class Implementation
	# Is the implementation mutable in the future ?
	var is_mutable: Bool

	# Execute an attribute access
	# *`recv` The receiver
	# *`value` The value to write, null if the implementation is an attribute read
	# Return the read value if self is an attribute read
	fun exec_attribute(recv: MutableInstance, value: nullable Instance): nullable Instance is abstract

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

	# The site which contains self
	var mosite: MOSite

	# The (global if SST, relative if PH) offset of the property
	var offset: Int

	# The PIC of the implementation (not loaded at compile-time)
	var pic: MClass

	# A NullImpl must load the corresponding class and execute it
	# At compile-time the receiver class was not loaded yet
	redef fun exec_attribute(recv, value)
	do
		# Execute a trampoline for this site (i.e. replace it by a PH implementation)
		var impl = trampoline(recv)

		# We execute the PHImpl
		var res = impl.exec_attribute(recv, value)

		if value == null and res == null then
			print "Problème recv {recv}"
		end

		# We replace the implementation in the corresponding site by a new one
		mosite.impl = impl

		# Finally, return the read value if any
		return res
	end

	# The method load the PIC (the class which introduced the property),
	# Then it creates a new PHImpl for this site and return it
	fun trampoline(recv: Instance): PHImpl
	do
		sys.vm.load_class(recv.mtype.as(MClassType).mclass)

		return new PHImpl(true, offset, pic.vtable.id)
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

	redef fun exec_attribute(recv, value)
	do
		# If this is an attribute read
		if value == null then
			return sys.vm.read_attribute_sst(recv.internal_attributes, offset)
		else
			sys.vm.write_attribute_sst(recv.internal_attributes, offset, value)
			return null
		end
	end

	redef fun exec_method(recv: Instance): MMethodDef is abstract

	redef fun exec_subtype(recv: Instance): Bool is abstract
end

# Perfect hashing implementation
class PHImpl
	super ObjectImpl

	# The target identifier of the subtyping-test or the class which introduced the GP
	var id: Int

	redef fun exec_attribute(recv, value)
	do
		# If this is an attribute read
		if value == null then
			return sys.vm.read_attribute_ph(recv.internal_attributes, recv.vtable.internal_vtable, recv.vtable.mask, id, offset)
		else
			# Attribute write
			sys.vm.write_attribute_ph(recv.internal_attributes, recv.vtable.internal_vtable, recv.vtable.mask, id, offset, value)
			return null
		end
	end
end

# Common class for static implementation between subtypes, attr, meth.
abstract class StaticImpl
	super Implementation
end

# Static implementation (used only for method call)
class StaticImplProp
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
end
