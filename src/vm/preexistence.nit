# Compute preexistence of each objets sites in alives methods
module preexistence

import model_optimizations

# TODO: preexist_analysed is used because there is not "is_compiled" boolean of MPropDef (only on APropdef),
# and we need to know for preexistence analysis if a candidate local property is compiled or not.

redef class ToolContext
	# Disable inter-procedural analysis and 'new' cases
	var disable_preexistence_extensions = new OptionBool("Disable preexistence extensions", "--no-preexist-ext")

	# Disable inter-procedural analysis
	var disable_method_return = new OptionBool("Disable preexistence extensions on method call", "--disable-meth-return")

	redef init
	do
		super
		option_context.add_option(disable_preexistence_extensions)
		option_context.add_option(disable_method_return)
	end
end

redef class Sys
	# Tell if preexistence extensions are disabled
	var disable_preexistence_extensions: Bool is noinit

	# Tell if inter-procedural analysis is disabled
	var disable_method_return: Bool is noinit
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule, arguments)
	do
		sys.disable_preexistence_extensions = toolcontext.disable_preexistence_extensions.value
		sys.disable_method_return = toolcontext.disable_method_return.value
		super(mainmodule, arguments)
	end
end

redef class VirtualMachine
	redef fun load_class(mclass)
	do
		if mclass.loaded then return
		super(mclass)
	end
end

redef class MPropDef
	# Tell if preexistance analysis is done
	var preexist_analysed: Bool = false is writable

	# List of mutable preexists expressions
	var exprs_preexist_mut = new List[MOExpr]

	# List of mutable non preexists expressions
	var exprs_npreexist_mut = new List[MOExpr]

	# List of mutable expressions
	var preexist_mut_exprs = new List[MOExpr]

	# Drop exprs_preesit_mut and set unknown state to all expression inside
	# If the return_expr is in it, recurse on callers
	fun propage_preexist
	do
		for expr in preexist_mut_exprs do expr.preexist_init
		preexist_mut_exprs.clear

		if not disable_method_return then
			for p in callers do
				# p.as(MOCallSitePattern).propage_preexist
			end
		end
	end

	# Drop exprs_npreesit_mut and set unknown state to all expression inside
	# If the return_expr is in it, recurse on callers
	fun propage_npreexist
	do
		for expr in preexist_mut_exprs do expr.preexist_init
		preexist_mut_exprs.clear

		if not disable_method_return then
			for p in callers do
				p.as(MOCallSitePattern).propage_npreexist
			end
		end
	end

	var recursive_origin: Bool = false

	# The origin of the preexistence of self return variable (if any)
	fun preexistence_origin: Int
	do
		if recursive_origin then
			return 64
		else
			recursive_origin = true
			return return_expr.preexistence_origin
		end
	end
end

redef class Int
	# bit 1 preexistence
	# bit 2 immutable (si pre)
	# bit 4 value preexistence
	# bit 8 non-preexistence
	# bit 16 immutable (si non-pre)
	# bit 32 recursif
	# bit 64 self
	# bit >128 autres paramètres
	# bit 1-4 -> and
	# bit 8-- -> or
	fun check_preexist: Bool
	do
		# invariant d'une préexistence complètement calculée
		var low = bin_and(63)
		var preexist_values = once [0,1,0,3,0,5,0,7,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
		if low != preexist_values[low] then
			print("Preexistence of {self} = {low}")
			return false
		end

		if self > 32 then
			if not low < 8 then
				print("Preexistence of {self} = {low}")
				return false
			end
		end

		return true
	end

	fun bit_param(n: Int): Bool
	do
		return bin_and(64.lshift(n)) > 0
	end

	fun bit_rec: Bool
	do
		return bin_and(32) == 32
	end

	fun bit_pre: Bool
	do
		return bin_and(1) == 1
	end

	fun bit_pre_immut : Bool
	do
		return bin_and(2) == 2
	end

	fun bit_pre_val: Bool
	do
		return bin_and(4) == 4
	end

	fun bit_npre: Bool
	do
		return bin_and(8) == 8
	end

	fun bit_npre_immut: Bool do
		return bin_and(16) == 16
	end

	fun bit_mut: Bool do
		return bin_and(18) == 0
	end

	fun bit_immut: Bool do
		return bin_and(18) > 0
	end

	fun bit_unknown: Bool do
		return self < 0
	end

	fun merge(n: Int): Int
	do
		check_preexist
		n.check_preexist

		var low = bin_and(n)
		var high = bin_or(n)

		if high.bit_npre then return high.bin_and(24)
		if high.bit_rec then return 32

		high.check_preexist
		if low.bit_pre_immut != high.bit_pre_immut then
			high = high.bin_and(-3)
		end

		if low.bit_pre_val != high.bit_pre_val then
			high = high.bin_and(-5)
		end

		return high
	end

	# Display 8 lower bits of preexistence value
	fun preexists_bits: Array[Int]
	do
		var bs = bits.reversed
		for i in [0..23] do bs.shift
		return bs
	end
end

redef class MOExpr
	# Allows to trace the preexistence origin of a Site by encoding the following values:
	# 1: parameter
	# 2: a new
	# 4: a call
	# 8: a lit
	# 16: a primitive
	# 32: null receiver
	# 64: recursive
	# 128: is_npre
	# 256: the receiver is a readsite
	fun preexistence_origin: Int
	do
		if is_pre then
			return 0
		else
			return 128
		end
	end

	fun preexistence_origin_recursive: Int
	do
		return preexistence_origin
	end

	# Return true if the expression preexists (recursive case is interpreted as preexistent)
	fun is_pre: Bool do return expr_preexist.bit_pre

	# True true if the expression non preexists
	fun is_npre: Bool do return not is_pre

	# Use this instead of init_preexist
	fun preexist_init do preexist_value = -1

	# The default value of preexistence
	var preexist_value: Int = -1

	fun expr_preexist: Int
	do
		if preexist_value.bit_unknown then

			preexist_value = compute_preexist

			if not preexist_value.check_preexist then
				print "{self}"
			end

			if preexist_value.bit_mut then lp.preexist_mut_exprs.add(self)
		end

		return preexist_value
	end

	fun compute_preexist: Int is abstract
end

redef class MOParam
	redef fun compute_preexist
	do
		preexist_value = 64.lshift(offset)+7
		preexist_value.check_preexist

		return preexist_value
	end

	redef fun preexistence_origin: Int
	do
		return super.bin_or(1)
	end
end

redef class MOVar
	fun return_preexist: Int
	do
		if preexist_value.bit_unknown then
			preexist_value = 32

			preexist_value = compute_preexist
			if not preexist_value.check_preexist then print(self.to_s)

			# If the preexistence of the return can changed, add it to the mutables list
			if preexist_value.bit_mut then lp.preexist_mut_exprs.add(self)
		end

		return preexist_value
	end
end

redef class MOSSAVar
	redef fun compute_preexist
	do
		return dependency.expr_preexist
	end

	redef fun preexistence_origin: Int
	do
		return dependency.preexistence_origin
	end
end

redef class MOPhiVar
	redef fun compute_preexist
	do
		print "compute_preexist for {self} {dependencies}"
		var preval = 0
		for dep in dependencies do
			if preval == 0 then
				preval = dep.expr_preexist
			else
				preval = preval.merge(dep.expr_preexist)
			end
		end
		return preval
	end

	redef fun preexistence_origin: Int
	do
		var res = 0
		for dep in dependencies do
			res = res.bin_or(dep.preexistence_origin)
		end

		return res
	end
end

redef class MOSite
	fun site_preexist: Int
	do
		return expr_recv.expr_preexist
	end
end

redef class MOCallSite
	redef fun compute_preexist
	do
		# If the preexistence extension is deactivated, the callsite is not preexistant
		if disable_preexistence_extensions or disable_method_return then
			return 8
		end

		var callees: nullable List[MPropDef]
		var gp = pattern.gp
		var preval = 0

		if concretes_receivers != null then
			callees = concretes_callees

			for callee in callees do
				if not callee.is_compiled then return 8
			end
		else
			if pattern.cuc > 0 then return 8
			callees = pattern.callees
			if callees.length == 0 then return 1
		end

		nb_callees = callees.length
		for lp in callees do
			var prelp: Int
			if lp.as(MMethodDef).is_abstract then
				# By default, a method is preexisting
				prelp = 7
			else
				prelp = lp.return_expr.return_preexist
			end

			if preval == 0 then
				preval = prelp
			else
				preval = preval.merge(prelp)
			end
		end

		if preval.bit_npre then return preval

		var rec: Bool = false
		var pval: Int
		if preval.bit_rec then
			pval = -63
			rec = true
		else
			pval = preval.bin_and(63)
		end

		# If preexisting, we filter by arguments and erase the dependances in the callee
		pval = preval.bin_and(63)

		# And we combine with the one of the caller
		if preval.bit_param(0) then pval = pval.merge(expr_recv.expr_preexist)

		var n = 0
		for arg in given_args do
			n += 1
			if preval.bit_param(n) then pval = pval.merge(arg.expr_preexist)
		end

		if rec and pval.bit_pre then
			return 32
		else
			# If we do not have any receivers
			if concretes_receivers == null and pval.bit_pre_immut then
				return pval.setbit(2, 0)
			end

			return pval
		end
	end

	redef fun preexistence_origin: Int
	do
		return super.bin_or(4)
	end

	redef fun preexistence_origin_recursive: Int
	do
		var callees: nullable List[MPropDef]
		var gp = pattern.gp

		if get_concretes != null then
			callees = new List[MPropDef]
			for rcv in concretes_receivers.as(not null) do
				callees.add_all(pattern.callees)
			end
		else
			callees = pattern.callees
			if callees.length == 0 then return 32
		end

		var res = 0
		for lp in callees do
			res = res.bin_or(lp.return_expr.preexistence_origin_recursive)
		end

		return res
	end

	var nb_callees = 0

	# Trace the origin of preexistence of a site
	# 1: positive cuc
	# 2: at least one preexisting callee
	# 4: at least one non-preexisting callee
	# 8: the callee is a procedure
	# 16: the expression is preexisting
	# 32: concretes types
	# 64: generic/formal receiver
	fun trace_origin: Int
	do
		var res = 0
		if pattern.cuc > 0 then res = res.bin_or(1)

		# Search for a preexisting (or not) return of a callee
		for callee in pattern.callees do
			if callee.return_expr == null then
				res = res.bin_or(8)
			else
				if callee.return_expr.is_pre then
					res = res.bin_or(2)
				else
					res = res.bin_or(4)
				end
			end
		end

		if is_pre then res = res.bin_or(16)

		if concretes_receivers != null then res = res.bin_or(32)

		if ast.get_receiver.mtype isa MFormalType then res = res.bin_or(64)

		return res
	end
end

redef class MMethodDef
	# Compute the preexistence of all invocation sites of the method
	# Return true if the method is analysed, false otherwise (already compiled, extern or extern method)
	#
	# WARNING!
	# The VM can't interpret FFI code, so intern/extern methods are not analysed,
	# and a expression using a receiver from intern/extern method is preexistent.
	#
	fun preexist_all(vm: VirtualMachine): Bool
	do
		if preexist_analysed or is_intern or is_extern then return false
		preexist_analysed = true

		var preexist: Int

		if not disable_preexistence_extensions then
			for newexpr in monews do
				assert not newexpr.pattern.cls.mclass_type.is_primitive_type

				preexist = newexpr.expr_preexist
			end
		end

		# If a returnvar is present, then compute its preexistence
		if return_expr != null then
			var pre = return_expr.return_preexist
		end

		for site in mosites do
			preexist = site.site_preexist
		end

		return true
	end

	redef fun compile_mo
	do
		super

		preexist_all(vm)
	end
end

redef class MOSuper
	redef fun compute_preexist
	do
		# A Super is always preexisting
		return 1
	end

	redef fun preexistence_origin: Int
	do
		return super.bin_or(4)
	end
end

redef class MOLit
	redef fun compute_preexist
	do
		return 7
	end

	redef fun preexistence_origin: Int
	do
		return super.bin_or(8)
	end
end

redef class MOAsSubtypeSite
	redef fun compute_preexist
	do
		return expr_recv.expr_preexist
	end

	redef fun preexistence_origin: Int
	do
		return expr_recv.preexistence_origin
	end
end

redef class MOIsaSubtypeSite
	redef fun compute_preexist
	do
		return 3
	end
end

redef class MOAsNotNullSite
	redef fun compute_preexist
	do
		return expr_recv.expr_preexist
	end

	redef fun preexistence_origin: Int
	do
		return expr_recv.preexistence_origin
	end
end

redef class MONew
	redef fun compute_preexist
	do
		if disable_preexistence_extensions then
			# Non perennial and not preexistant
			return 24
		else if pattern.is_loaded then
			# Preexisting and perennial
			return 3
		else
			# Non-preexisting and non perennial
			return 8
		end
	end

	redef fun preexistence_origin: Int
	do
		return super.bin_or(2)
	end
end

redef class MONull
	redef fun preexist_init do end
end

redef class MOPrimitive
	redef fun compute_preexist
	do
		return 7
	end

	redef fun preexistence_origin: Int
	do
		return super.bin_or(16)
	end
end

redef class MOReadSite
	redef fun compute_preexist
	do
		# For now, an attribute read is non-preexisting perennial
		return 24
	end

	redef fun preexistence_origin: Int
	do
		return super.bin_or(256)
	end
end

redef class MOCallSitePattern
	# If a LP no preexists and it's perexistence is perennial (unused while cuc > 0)
	var perennial_status = false

	# If all LPs preexists and are perennial, according to the current class hierarchy
	var lp_all_perennial = false

	# Call MMethodDef.propage_preexist on all callees
	fun propage_preexist
	do
		for lp in callees do lp.propage_preexist
	end

	# Call MMethodDef.propage_npreexist on all callees
	fun propage_npreexist
	do
		for lp in callees do lp.propage_npreexist
	end

	# When add a new branch, if it is not compiled, unset preexistence to all expressions using it
	redef fun add_lp(lp)
	do
		super

		if cuc == 1 then
			for site in sites do
				site.expr_recv.preexist_init
				site.lp.propage_preexist
				site.lp.preexist_analysed = false
			end
		end
	end

	# Return true if all sites of this pattern are preexisting, else false
	fun is_pre: Bool
	do
		if cuc != 0 then return false

		if callees.length == 0 then return false

		for callee in callees do
			#TODO : le cuc doit être null ici, donc les méthodes avec un return_expr
			if callee.return_expr != null then
				if not callee.return_expr.return_preexist.bit_pre then return false
			end
		end


		return true
	end
end

#TODO: propagation
