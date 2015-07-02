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
		if not disable_preexistence_extensions then mclass.new_pattern.set_preexist_newsite
	end
end

redef class MPropDef
	# Tell if preexistance analysis is done
	var preexist_analysed: Bool = false is writable

	# List of mutable preexists expressions
	var exprs_preexist_mut = new List[MOExpr]

	# List of mutable non preexists expressions
	var exprs_npreexist_mut = new List[MOExpr]

	var preexist_mut_exprs = new List[MOExpr]

	# Drop exprs_preesit_mut and set unknown state to all expression inside
	# If the return_expr is in it, recurse on callers
	fun propage_preexist
	do
		var flag = false
		if self isa MMethodDef then
			if return_expr_is_object then flag = return_expr.as(not null).is_pre_nper
		end

		for expr in exprs_preexist_mut do expr.init_preexist
		exprs_preexist_mut.clear
		preexist_mut_exprs.clear

		if flag and not disable_method_return then for p in callers do p.as(MOCallSitePattern).propage_preexist
	end

	# Drop exprs_npreesit_mut and set unknown state to all expression inside
	# If the return_expr is in it, recurse on callers
	fun propage_npreexist
	do
		var flag = false
		if self isa MMethodDef then
			if return_expr_is_object then flag = return_expr.as(not null).is_npre_nper
		end

		for expr in exprs_npreexist_mut do expr.init_preexist
		exprs_npreexist_mut.clear
		preexist_mut_exprs.clear

		if flag and not disable_method_return then for p in callers do p.as(MOCallSitePattern).propage_npreexist
	end

	# Fill the correct list if the analysed preexistence if unperennial
	fun fill_nper(expr: MOExpr)
	do
		if expr.is_nper then
			if expr.is_pre then
				if not exprs_preexist_mut.has(expr) then exprs_preexist_mut.add(expr)
			else
				if not exprs_npreexist_mut.has(expr) then exprs_npreexist_mut.add(expr)
			end
		end
	end
end

redef class Int
	# bit 1 preexistence
	# bit 2 immutable (si pre)
	# bit 3 value preexistence
	# bit 4 non-preexistence
	# bit 5 immutable (si non-pre)
	# bit 6 recursif
	# bit 7 self
	# bit >7 autres paramètres
	# bit 1-3 -> and
	# bit 4-- -> or
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

	# Display 8 lower bits of preexitence value
	fun preexists_bits: Array[Int]
	do
		var bs = bits.reversed
		for i in [0..23] do bs.shift
		return bs
	end
end

redef class MOExpr
	# The cached preexistence of the expression (the return of the expression)
	var preexist_expr_value: Int = pmask_UNKNOWN

	# Compute the preexistence of the expression
	fun preexist_expr: Int is abstract

	# Set a bit in a dependency range on the given offset to a preexistence state
	# Shift 4 bits (preexistence status) + the offset of dependency, and set bit to 1
	fun set_dependency_flag(offset: Int): Int
	do
		preexist_expr_value = preexist_expr_value.bin_or(1.lshift(4 + offset))
		return preexist_expr_value
	end

	# True if the expression depends of the preexistence of a dependencie at `index`
	fun is_dependency_flag(index: Int): Bool
	do
		# It must concern a dependency bit
		index += 5

		return 1.lshift(index).bin_and(preexist_expr_value) != 0
	end

	# Affect status mask
	private fun set_status_mask(mask: Int)
	do
		if is_pre_unknown or is_rec then preexist_expr_value = 0
		preexist_expr_value = preexist_expr_value.rshift(4).lshift(4).bin_or(mask)
	end

	# Set type preexist perennial
	fun set_ptype_per do set_status_mask(pmask_PTYPE_PER)

	# Set value preexist perennial
	fun set_pval_per do set_status_mask(pmask_PVAL_PER)

	# Set non preexist non perennial
	fun set_npre_nper do set_status_mask(pmask_NPRE_NPER)

	# Set non preexist perennial
	fun set_npre_per do preexist_expr_value = pmask_NPRE_PER

	# Set val preexist non perennial
	fun set_pval_nper do set_status_mask(pmask_PVAL_NPER)

	# Set recursive flag
	fun set_recursive do preexist_expr_value = pmask_RECURSIV

	# Return true if the preexistence of the expression isn't known
	fun is_pre_unknown: Bool do return preexist_expr_value == pmask_UNKNOWN

	# Return true if the expression is recursive
	fun is_rec: Bool do return preexist_expr_value == 0

	# Return true if the expression preexists (recursive case is interpreted as preexistent)
	fun is_pre: Bool do return expr_preexist.bit_pre

	# True true if the expression non preexists
	fun is_npre: Bool do return not is_pre

	# Return true if the preexistence state of the expression is perennial
	fun is_per: Bool do return preexist_expr_value.bin_and(4) == 4

	# Return true if the preexistence state if not perennial
	fun is_nper: Bool do return not is_per

	# Return true if the prexistence state is preexist and no perennial
	fun is_pre_nper: Bool do return is_pre and is_nper

	# Return true if the preexistence state is no preexist and no perennial
	fun is_npre_nper: Bool do return is_npre and is_nper

	# Return true if the preexistence state is no preexist and perennial
	fun is_npre_per: Bool do return is_npre and is_per

	# Initialize preexist_cache to UNKNOWN
	fun init_preexist do preexist_expr_value = pmask_UNKNOWN

	fun preexist_init do preexist_value = -1

	# Merge dependecies and preexistence state
	fun merge_preexistence(expr: MOExpr): Int
	do
		if expr.is_npre_per then
			set_npre_per
		else if expr.is_rec then
			set_recursive
		else
			var pre = preexist_expr_value.bin_and(15)
			var deps = preexist_expr_value.rshift(4).lshift(4)

			pre = pre.bin_and(expr.preexist_expr_value.bin_and(15))
			deps = deps.bin_or(expr.preexist_expr_value.rshift(4).lshift(4))

			preexist_expr_value = pre.bin_or(deps)
		end

		return preexist_expr_value
	end

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
	redef var preexist_expr_value = pmask_PVAL_PER

	init
	do
		set_dependency_flag(offset)
	end

	redef fun compute_preexist
	do
		preexist_value = 64.lshift(offset)+7
		preexist_value.check_preexist

		return preexist_value
	end

	redef fun preexist_expr do return preexist_expr_value
end

redef class MOVar
	fun return_preexist: Int
	do
		if preexist_value.bit_unknown then
			preexist_value = 32

			preexist_value = compute_preexist
			if not preexist_value.check_preexist then print(self.to_s)

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

	redef fun preexist_expr
	do
		if is_pre_unknown then preexist_expr_value = dependency.preexist_expr
		return preexist_expr_value
	end
end

redef class MOPhiVar
	redef fun compute_preexist
	do
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

	redef fun preexist_expr
	do
		if is_pre_unknown then
			preexist_expr_value = pmask_PVAL_PER
			for dep in dependencies do
				dep.preexist_expr
				merge_preexistence(dep)
				if is_npre_per then
					break
				end
			end
		end

		return preexist_expr_value
	end
end

redef class MOSite
	fun site_preexist: Int
	do
		expr_recv.expr_preexist

		if expr_recv.preexist_value.bit_rec then
			expr_recv.preexist_value = 32.lshift(20) - 63
		end

		return expr_recv.preexist_value
	end

	# # Compute the preexistence of the site call
	fun preexist_site: Int
	do
		expr_recv.preexist_expr
		if expr_recv.is_rec then expr_recv.set_pval_nper
		return expr_recv.preexist_expr_value
	end
end

redef class MOCallSite
	redef fun compute_preexist
	do
		# If the preexistence extension is deactivated, the callsite is not preexistant
		if disable_preexistence_extensions or disable_method_return then
			return 8
		end

		if pattern.cuc > 0 then return 8

		var callees: nullable List[MPropDef]
		var gp = pattern.gp
		var preval = 0

		if concretes_receivers != null then
			callees = new List[MPropDef]
			for rcv in concretes_receivers.as(not null) do
				callees.add_all(pattern.callees)
			end
		else
			callees = pattern.callees
			if callees.length == 0 then return 1
		end

		for lp in callees do
			var prelp = lp.return_expr.return_preexist
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
			# à vérifier
			pval = -63
			rec = true
		else
			pval = preval.bin_and(63)
		end

		## si preexistant on filtre par arguments
		## on efface les dépendances dans le callee
		pval = preval.bin_and(63)
		## et on combine avec celles du caller
		if preval.bit_param(0) then pval = pval.merge(expr_recv.expr_preexist)

		var n = 0
		for arg in given_args do
			n += 1
			if preval.bit_param(n) then pval = pval.merge(arg.expr_preexist)
		end

		if rec and pval.bit_pre then
			return 32
		else
			# Si le graphe d'appel est clos
			if concretes_receivers == null and pval.bit_pre_immut then
				return pval.setbit(2, 0)
			end

			return pval
		end
	end

	# If the receiver expression of `self` depends of the preexistence of the arg at `index`,
	# check if `expr` depends of the preexistence of the same arg.
	fun dep_matches(expr: MOExpr, index: Int): Bool
	do
		if is_dependency_flag(index) and not expr.is_dependency_flag(index) then
			return false
		end

		return true
	end

	# Check if the preexistence of the arguments matches with the dependencies of the expression
	# Then, merge the preexsitence values of all arguments with the expression preexistence
	fun check_args: Int
	do
		var index = 0

		for arg in given_args do
			arg.preexist_expr
			if dep_matches(arg, index) then
				merge_preexistence(arg)
			else
				set_npre_nper
				return preexist_expr_value
			end
			index += 1
		end

		return preexist_expr_value
	end

	redef fun preexist_expr
	do
		if disable_preexistence_extensions or disable_method_return then
			preexist_expr_value = pmask_NPRE_PER
		else if pattern.cuc > 0 then
			preexist_expr_value = pmask_NPRE_NPER
		else if pattern.perennial_status then
			preexist_expr_value = pmask_NPRE_PER
		else if pattern.lp_all_perennial then
			preexist_expr_value = pmask_PVAL_PER
			check_args
		else if pattern.callees.length == 0 then
			set_npre_nper
		else
			preexist_expr_value = pmask_UNKNOWN
			for candidate in pattern.callees do
				if candidate.is_intern or candidate.is_extern then
					# WARNING
					# If the candidate method is intern/extern, then the return is preexist immutable
					# since the VM cannot make FFI.
					set_pval_per
					break
				else if not candidate.preexist_analysed then
					# The lp could be known by the model but not already compiled from ast to mo
					# So, we must NOT check it's return_expr (it could be still null)
					trace("WARNING, this should not happen")
					set_npre_nper
					break
				else if not candidate.return_expr_is_object then
					# Lazy attribute not yet initialized
					# WARNING
					# Be sure that it can't be anything else that lazy attributes here
					trace("WARN NULL RETURN_EXPR {candidate} {candidate.mproperty}")
					set_npre_nper
					break
				end

				candidate.preexist_return

				if preexist_expr_value == pmask_UNKNOWN then
					preexist_expr_value = candidate.return_expr.preexist_expr_value
				else
					merge_preexistence(candidate.return_expr.as(not null))
				end

				if is_npre_per then
					break
				else
					check_args
				end
			end
		end

		return preexist_expr_value
	end
end

redef class MMethodDef
	# Compute the preexistence of the return of the method expression
	fun preexist_return: Int
	do
		# preexist_return is called only when return_expr is not null
		var expr = return_expr.as(not null)

		if not preexist_analysed then
			expr.set_npre_nper
		else if expr.is_pre_unknown then
			expr.set_recursive
			expr.preexist_expr

			if expr.is_rec then
				expr.set_pval_nper
			end
		end

		return expr.preexist_expr_value
	end

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

		trace("\npreexist_all of {self}")
		var preexist: Int

		if not disable_preexistence_extensions then
			for newexpr in monews do
				assert not newexpr.pattern.cls.mclass_type.is_primitive_type

				preexist = newexpr.preexist_expr
				fill_nper(newexpr)
				trace("\tpreexist of new {newexpr} loaded:{newexpr.pattern.is_loaded} {preexist} {preexist.preexists_bits}")
			end
		end

		for site in mosites do
			preexist = site.site_preexist
			var buff = "\tpreexist of "

			fill_nper(site.expr_recv)

			if site isa MOAttrSite then
				buff += "attr {site.pattern.rst}.{site.pattern.gp}"
			else if site isa MOSubtypeSite then
				buff += "cast {site.pattern.rst} isa {site.target}"
			else if site isa MOCallSite then
				buff += "meth {site.pattern.rst}.{site.pattern.gp}"
			else if site isa MOAsNotNullSite then
				buff += "cast not null {site.pattern.rst}"
			else
				abort
			end

			buff += " {site.expr_recv}.{site} {preexist} {preexist.preexists_bits}"
			trace(buff)
			trace("\t\tconcretes receivers? {(site.get_concretes.length > 0)}")
		end

		if exprs_preexist_mut.length > 0 then trace("\tmutables pre: {exprs_preexist_mut}")
		if exprs_npreexist_mut.length > 0 then trace("\tmutables nper: {exprs_npreexist_mut}")

		return true
	end

	redef fun compile_mo
	do
		super

		preexist_all(vm)
	end
end

# Preexistence masks
# PVAL_PER:	0...1111
# PTYPE_PER:	0...1101
# PVAL_NPER:	0...1011
# PTYPE_NPER:	0...1001
# NPRE_PER:	0...1100
# NPRE_NPER:	0...1000
# RECURSIV:	0...0000
# PRE_PER:	0...0101
# PRE_NPER:	0...0001
# UNKNOWN:	1...

# Preexistence mask of perennial value preexistence
fun pmask_PVAL_PER: Int do return 15

# Preexistence mask of perennial type preexistence
fun pmask_PTYPE_PER: Int do return 13

# Preexistence mask of no perennial value preexistence
fun pmask_PVAL_NPER: Int do return 11

# Preexistence mask of no perennial type preexistence
fun pmask_PTYPE_NPER: Int do return 9

# Preexistence mask of perennial no preexistence
fun pmask_NPRE_PER: Int do return 12

# Preexistence mask of no perennial no preexistence
fun pmask_NPRE_NPER: Int do return 8

# Preexistence mask of recursive calls
fun pmask_RECURSIV: Int do return 0

# Preexistence mask of unknown preexistence
fun pmask_UNKNOWN: Int do return 255

redef class MOSuper
	redef fun preexist_expr
	do
		if is_pre_unknown then set_pval_per
		return preexist_expr_value
	end

	redef fun compute_preexist
	do
		# A Super is always preexisting
		return 1
	end
end

redef class MOLit
	redef fun compute_preexist
	do
		return 7
	end

	redef fun preexist_expr
	do
		if is_pre_unknown then set_pval_per
		return preexist_expr_value
	end
end

redef class MOAsSubtypeSite
	redef fun preexist_expr
	do
		if is_pre_unknown then preexist_expr_value = expr_recv.preexist_expr
		return preexist_expr_value
	end

	redef fun compute_preexist
	do
		return expr_recv.expr_preexist
	end
end

redef class MOIsaSubtypeSite
	redef fun preexist_expr
	do
		if is_pre_unknown then set_npre_per
		return preexist_expr_value
	end

	redef fun compute_preexist
	do
		return 3
	end
end

redef class MOAsNotNullSite
	redef fun preexist_expr
	do
		if is_pre_unknown then preexist_expr_value = expr_recv.preexist_expr
		return preexist_expr_value
	end

	redef fun compute_preexist
	do
		return expr_recv.expr_preexist
	end
end

redef class MONew
	redef fun init_preexist do
		if disable_preexistence_extensions then
			set_npre_per
		else if pattern.is_loaded then
			set_ptype_per
		else
			set_npre_nper
		end
	end

	redef fun preexist_expr do
		if is_pre_unknown then init_preexist
		return preexist_expr_value
	end

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
end

redef class MONull
	redef var preexist_expr_value = pmask_PVAL_PER

	redef fun init_preexist do end

	redef fun preexist_expr do return preexist_expr_value
end

redef class MOPrimitive
	redef fun compute_preexist
	do
		return 7
	end

	redef fun preexist_expr
	do
		if is_pre_unknown then set_pval_per
		return preexist_expr_value
	end
end

redef class MOReadSite
	redef fun preexist_expr
	do
		if is_pre_unknown then
			expr_recv.preexist_expr
			if immutable then
				if expr_recv.is_pre then
					if expr_recv.is_per then
						set_pval_per
					else
						set_pval_nper
					end

					# The receiver is always at position 0 of the environment
					set_dependency_flag(0)
				else
					if expr_recv.is_per then
						set_npre_per
					else
						set_npre_nper
					end
				end
			else
				set_npre_per
			end
		end

		return preexist_expr_value
	end

	redef fun compute_preexist
	do
		# For now, an attribute read is non-preexisting perennial
		return 24
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
				site.expr_recv.init_preexist
				site.lp.propage_preexist
				site.lp.preexist_analysed = false
			end
		end
	end
end

redef class MONewPattern
	# Set npreexist new site preexistent
	# The non preexistence of newsite became preesitent if class is loaded
	fun set_preexist_newsite
	do
		for newexpr in newexprs do
			newexpr.set_ptype_per
			newexpr.lp.propage_npreexist
		end
	end
end
