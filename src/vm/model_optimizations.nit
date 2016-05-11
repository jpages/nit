# Intermediate representation of nit program running inside the VM
module model_optimizations

import concrete_types
import compilation

redef class ToolContext
	# Enable traces of analysis
	var trace_on = new OptionBool("Display the trace of model optimizing / preexistence analysis", "--mo-trace")

	# If true, the execution is verified to test the model
	var debug = new OptionBool("Launch the execution in debug mode", "--debug")

	# If true, the vm will load all top-level news she met in methods during compilation
	var improve_loading = new OptionBool("Load all top-level news in the code during compilation", "--improve-loading")

	# Disable inter-procedural analysis and 'new' cases
	var disable_preexistence_extensions = new OptionBool("Disable preexistence extensions", "--no-preexist-ext")

	# Disable inter-procedural analysis
	var disable_method_return = new OptionBool("Disable preexistence extensions on method call", "--disable-meth-return")

	# If true, consider the preexistence of sites in the protocol
	var preexistence_protocol = new OptionBool("Consider sites' preexistence in the protocol", "--preexistence-protocol")

	# A mix between code-patching and preexistence
	var mixed_protocol = new OptionBool("Consider preexistence for all site except callsites", "--mixed-protocol")

	redef init
	do
		super
		option_context.add_option(trace_on)
		option_context.add_option(debug)
		option_context.add_option(improve_loading)
		option_context.add_option(disable_preexistence_extensions)
		option_context.add_option(disable_method_return)
		option_context.add_option(preexistence_protocol)
		option_context.add_option(mixed_protocol)
	end
end

redef class Sys
	# Tell if preexistence extensions are disabled
	var disable_preexistence_extensions: Bool is noinit

	# Tell if inter-procedural analysis is disabled
	var disable_method_return: Bool is noinit

	# Display trace if --mo-trace is set
	fun trace(buf: String) do if trace_on then print(buf)

	# Tell if trace is enabled
	var trace_on: Bool is noinit

	# The trace file for debug the model, see the option `debug`
	var debug_file: FileWriter is noinit

	# The debug mode of the virtual machine
	var debug_mode: Bool = false

	# If true, improve the loading of classes
	var improve_loading: Bool = false

	# Use preexistence values in the protocol, and recompile the whole method instead,
	# of doing code-patching
	var preexistence_protocol: Bool = false

	# See --mixed-protocol option
	var mixed_protocol: Bool = false

	# Singleton of MONull
	var monull = new MONull(sys.vm.current_propdef.mpropdef.as(not null)) is lazy

	# Singleton of MOPrimitive
	var moprimitive = new MOPrimitive(sys.vm.current_propdef.mpropdef.as(not null)) is lazy

	# Singleton of MOLiteral
	var moliteral = new MOLit(sys.vm.current_propdef.mpropdef.as(not null)) is lazy
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule, arguments)
	do
		sys.trace_on = toolcontext.trace_on.value
		sys.debug_mode = toolcontext.debug.value
		sys.improve_loading = toolcontext.improve_loading.value

		sys.disable_preexistence_extensions = toolcontext.disable_preexistence_extensions.value
		sys.disable_method_return = toolcontext.disable_method_return.value
		sys.preexistence_protocol = toolcontext.preexistence_protocol.value
		sys.mixed_protocol = toolcontext.mixed_protocol.value

		if toolcontext.debug.value then
			# Create the output file for debug traces
			sys.debug_file = new FileWriter.open("debug_file.txt")
		end

		var global_analysis = new GlobalAnalysis(self, mainmodule)
		global_analysis.get_stats

		super(mainmodule, arguments)

		if toolcontext.debug.value then
			# Create the output file for debug traces
			sys.debug_file.close
		end
	end
end

# A Pic pattern is an association between a Property Introduction Class represented by a position,
# and a class: the receiver class
class PICPattern
	# The class of the receiver static type
	var recv_class: MClass

	# The class of the property introduction class (the class of the global property)
	var pic_class: MClass

	# The collections of patterns
	var patterns = new List[MOPattern]

	# Add a MOPattern to `patterns`
	fun add_pattern(pattern: MOPattern)
	do
		patterns.add(pattern)
	end
end

# A PICPattern for an access inside a method table (a method call or a subtyping test)
class MethodPICPattern
	super PICPattern
end

# A PICPattern for an access inside the attribute table
class AttributePICPattern
	super PICPattern
end

# Superclass of all patterns
class MOPattern
end

# Pattern of instantiation sites
class MONewPattern
	super MOPattern

	# Class associated to the pattern
	var cls: MClass

	# MONew expressions using this pattern
	var newexprs = new List[MONew]

	# Tell if the class is loaded
	fun is_loaded: Bool
	do
		return cls.loaded
	end
end

# Pattern of objects sites
abstract class MOSitePattern
	super MOPattern

	# Type of the sites that refer to this pattern
	type S: MOSite

	# Static type of the receiver
	var rst: MType

	# Static class of the receiver
	var rsc: MClass

	# List of expressions that refers to this pattern
	var sites = new List[S]

	# True if at least one site of this pattern was executed
	var is_executed: Bool = false

	# The associated PICPattern
	var pic_pattern: PICPattern is noinit

	fun init_abstract: SELF
	do
		sys.vm.all_patterns.add(self)

		# Create the associated PICPattern if not already created
		set_pic_pattern

		return self
	end

	# Associate self with its PICPattern, create it if not exist
	fun set_pic_pattern
	do
		# The PIC is the class which introduced the property of the current pattern
		var pic = get_pic(sys.vm)

		# See if the corresponding PICPattern already exists
		var found_pic_pattern = null

		for p in pic.pic_patterns do
			if p.recv_class == rsc and p.pic_class == pic then
				found_pic_pattern = p
				break
			end
		end

		if found_pic_pattern == null then
			# Create an appropriate PICPattern
			found_pic_pattern = pic_pattern_factory(rsc, pic)
			sys.vm.all_picpatterns.add(found_pic_pattern)
			pic.pic_patterns.add(found_pic_pattern)
		end

		# Just make the association
		found_pic_pattern.add_pattern(self)
		pic_pattern = found_pic_pattern
	end

	# Add a site
	fun add_site(site: S)
	do
		assert not sites.has(site)

		sites.add(site)
		site.pattern = self
	end

	# Get the pic
	fun get_pic(vm: VirtualMachine): MClass is abstract

	# Create the appropriate PICPattern for this pattern if not exist
	# `rsc` The class of the receiver
	# `pic` The class which introduced the called global property
	# Return the newly created PICPattern
	fun pic_pattern_factory(rsc: MClass, pic: MClass): PICPattern is abstract
end

# Pattern of properties sites (method call / attribute access)
abstract class MOPropSitePattern
	super MOSitePattern

	# Type of global properties
	type GP: MProperty

	# Type of local properties
	type LP: MPropDef

	redef type S: MOPropSite

	# The global property
	var gp: GP

	init
	do
		super
		gp.patterns.add(self)
	end

	fun compatible_site(site: MOPropSite): Bool is abstract

	redef fun get_pic(vm) do return gp.intro_mclassdef.mclass
end

# Pattern of expression sites (method call / read attribute)
abstract class MOExprSitePattern
	super MOSitePattern

	redef type S: MOExprSite
end

# Pattern of subtype test sites
class MOSubtypeSitePattern
	super MOExprSitePattern

	redef type S: MOSubtypeSite

	# Static type of the target
	var target: MType

	var target_mclass: MClass

	redef fun get_pic(vm) do return target.as(MClassType).mclass

	redef fun pic_pattern_factory(rsc, pic)
	do
		return new MethodPICPattern(rsc, pic)
	end
end

class MOAsNotNullPattern
	super MOExprSitePattern

	redef type S: MOAsNotNullSite

	redef fun get_pic(vm) do return rsc

	redef fun pic_pattern_factory(rsc, pic)
	do
		return new MethodPICPattern(rsc, pic)
	end
end

# Pattern of method call
class MOCallSitePattern
	super MOPropSitePattern
	super MOExprSitePattern

	redef type GP: MMethod

	redef type LP: MMethodDef

	redef type S: MOCallSite

	# Indicate if the corresponding property has a return,
	# if not, then this pattern references procedure sites
	var is_function: Bool

	# Candidates local properties owning by the GP
	var callees = new List[LP]

	# Number of calls on uncompiled methods
	var cuc = 0

	init(rst: MType, rsc: MClass, gp: MMethod, function: Bool)
	do
		super(rst, rsc, gp)

		self.gp = gp
		self.rst = rst
		self.rsc = rsc
		is_function = function

		if rsc.abstract_loaded then
			for subclass in rsc.loaded_subclasses do
				var lp_rsc = gp.lookup_first_definition(sys.vm.mainmodule, subclass.intro.bound_mtype)

				add_lp(lp_rsc)
			end
		end
	end

	redef fun compatible_site(site: MOPropSite)
	do
		return site isa MOCallSite
	end

	# Add a new local method to this pattern
	fun add_lp(mpropdef: LP)
	do
		if not gp.living_mpropdefs.has(mpropdef) then
			gp.living_mpropdefs.add(mpropdef)
		end

		if not callees.has(mpropdef) then
			callees.add(mpropdef)
			mpropdef.callers.add(self)

			# If the mpropdef is abstract do not count it in uncompiled methods
			if not mpropdef.is_abstract and not mpropdef.is_compiled then cuc += 1
		end
	end

	redef fun pic_pattern_factory(rsc, pic)
	do
		return new MethodPICPattern(rsc, pic)
	end

	# Decrement the number of uncompiled callees
	fun decrement_cuc
	do
		cuc -= 1
	end
end

# Common pattern of all attribute reads and writes
abstract class MOAttrPattern
	super MOPropSitePattern

	redef type GP: MAttribute

	redef type LP: MAttributeDef

	redef fun pic_pattern_factory(rsc, pic)
	do
		return new AttributePICPattern(rsc, pic)
	end
end

# Pattern of read attribute
class MOReadSitePattern
	super MOExprSitePattern
	super MOAttrPattern

	redef type S: MOReadSite

	redef fun compatible_site(site: MOPropSite)
	do
		return site isa MOReadSite
	end
end

# Pattern of write attribute
class MOWriteSitePattern
	super MOAttrPattern

	redef type S: MOWriteSite

	redef fun compatible_site(site: MOPropSite)
	do
		return site isa MOWriteSite
	end
end

redef class MProperty
	# Type of owning local properties
	type LP: MPropDef

	# Type of the pattern
	type PATTERN: MOPropSitePattern

	# List of patterns using this gp
	var patterns = new List[PATTERN] is lazy
end

redef class MPropDef
	# Type of the patterns who can use this local property
	type P: MOPropSitePattern

	# List of patterns who use this local property
	var callers = new List[P]

	var is_compiled: Bool = false

	# Classes to load at the end of compilation (relative to --improve-loading)
	var to_load = new HashSet[MClass]

	# Compile the property
	fun compile_mo
	do
		if self isa MMethodDef then
			var global_method = mproperty.as(MMethod)
			if not sys.vm.compiled_global_methods.has(global_method) then
				sys.vm.compiled_global_methods.add(global_method)
			end
		end

		sys.vm.compiled_mproperties.add(self)

		for mclass in to_load do
			sys.vm.load_class(mclass)
		end

		if not to_load.is_empty then to_load.clear

		for site in mosites do
			# Determine if the site is monomorphic
			site.monomorphic_analysis

			# Initialize concrete receivers of sites
			if not site.is_monomorph then site.compute_concretes_site
		end

		for pattern in callers do
			if pattern isa MOCallSitePattern then pattern.decrement_cuc
		end

		is_compiled = true
	end

	# Return expression of the propdef (null if procedure)
	var return_expr: nullable MOVar is noinit, writable

	# Return true if the return type of `self` is not a primitive object
	fun return_expr_is_object: Bool
	do
		if mproperty.intro isa MMethodDef and mproperty.intro.as(MMethodDef).msignature.return_mtype != null then
			return not mproperty.intro.as(MMethodDef).msignature.return_mtype.is_primitive_type
		else
			return true
		end
	end

	# List of instantiations sites in this local property
	var monews = new HashSet[MONew]

	# List of object sites in this local property
	var mosites = new HashSet[MOSite]

	# Sites with a primitive receiver
	var primitive_sites = new HashSet[MOSite]

	# The sites which are monomorphics
	var monomorph_sites = new HashSet[MOSite]

	# All MOVar inside the mpropdef, including self and returnvar
	var variables: Array[MOVar] = new Array[MOVar]
end

redef class MMethod
	redef type LP: MMethodDef

	redef type PATTERN: MOCallSitePattern

	redef fun add_propdef(mpropdef, vm)
	do
		super

		for pattern in patterns do
			# Verify that the class of `mpropdef` is a subclass of the pattern in which
			# we want to add this local method
			if sys.vm.is_subclass(mpropdef.mclassdef.mclass, pattern.rsc) then
				pattern.add_lp(mpropdef)
			end
		end

		# Analyze the concrete types of the return expression of the added propdef
		mpropdef.compute_concretes(vm)
	end
end

redef class MMethodDef
	redef type P: MOCallSitePattern

	# The concrete types of the method's return
	var concrete_types: nullable ConcreteTypes

	# Compute the concrete types of the return expression, and assign
	# `concrete_type`
	fun compute_concretes(vm: VirtualMachine): nullable ConcreteTypes
	do
		concrete_types = null

		# While the method is not compiled, we can just check whether its return type
		# is final or not
		if not msignature.return_mtype == null then
			# The method is not a procedure
			var mclass_return = msignature.return_mtype.as(not null).get_mclass(vm, self)

			if mclass_return.is_final then
				concrete_types = new ConcreteTypes
				concrete_types.add(mclass_return.as(not null))

				return concrete_types
			end
		end

		if not is_compiled then return null

		# If the method is compiled, analyze its return expression
		concrete_types = new ConcreteTypes

		# Compute the concrete type of the return expression
		return return_expr.compute_concretes(null)
	end
end


# Root hierarchy of MO entities
abstract class MOEntity

	# The local property containing this expression
	var lp: MPropDef is noautoinit

	# The corresponding ast node, if any
	var ast: nullable AExpr is noautoinit

	fun pretty_print(file: FileWriter)
	do
	end

	init(mpropdef: MPropDef, node: nullable AExpr)
	do
		lp = mpropdef
		ast = node
	end
end

# Root hierarchy of expressions
abstract class MOExpr
	super MOEntity

	init(mpropdef: MPropDef, node: nullable AExpr)
	do
		super(mpropdef, node)
		sys.vm.all_moexprs.add(self)
		ast = node
	end

	fun compute_concretes(concretes: nullable ConcreteTypes): nullable ConcreteTypes
	do
		# FinalSite rule
		if ast == null then return null
		if ast.mtype == null then return null

		var mclass = ast.mtype.get_mclass(sys.vm, lp)

		if mclass != null and mclass.is_final and mclass.loaded then
			concretes = new ConcreteTypes
			concretes.immutable = true
			concretes.add(mclass)
			return concretes
		else
			# By default, an expression does not have concretes
			return null
		end
	end
end

# MO of variables
abstract class MOVar
	super MOExpr

	# The Variable objet refered by this node
	var variable: Variable

	# The offset of the variable in its environment, or the position of parameter
	var offset: Int

	redef fun pretty_print(file: FileWriter)
	do
		file.write("{variable.name} ")
	end
end

# MO of variables with only one dependency
class MOSSAVar
	super MOVar

	# the expression that variable depends
	var dependency: MOExpr is noinit, writable

	redef fun compute_concretes(concretes)
	do
		var concrete = dependency.compute_concretes(concretes)

		return concrete
	end

	redef fun pretty_print(file: FileWriter)
	do
		super
		file.write("dep = {dependency}\n")
	end
end

# MO of variable with multiples dependencies
class MOPhiVar
	super MOVar

	# List of expressions that variable depends
	var dependencies = new List[MOExpr] is writable

	redef fun compute_concretes(concretes)
	do
		super

		if concretes == null then
			concretes = new ConcreteTypes
		end

		for dep in dependencies do
			var dependency_concretes = dep.compute_concretes(concretes)

			# All dependencies must be concretes
			if dependency_concretes == null then
				return null
			else
				# We merge the concretes with previous values
				for con in dependency_concretes do
					if not concretes.has(con) then concretes.add(con)
				end
			end
		end

		return concretes
	end

	redef fun pretty_print(file: FileWriter)
	do
		super
		file.write("deps = ")
		for dep in dependencies do
			if dep isa MOVar then
				file.write("{dep.variable.name}")
			else
				file.write("{dep.to_s}")
			end
		end
		file.write("\n")
	end
end

# MO of each parameters given to a call site
class MOParam
	super MOVar
end

# The special case of Self
class MOSelf
	super MOParam

	# The class of self
	var self_mclass: MClass is noinit

	init(lp: MPropDef, node: AExpr, v: Variable, pos: Int)
	do
		super(lp, node)

		ast = node
		# Set self_mclass, the static type of self
		self_mclass = lp.mclassdef.mclass
		lp.mclassdef.mclass.self_sites.add(self)
	end

	# redef fun compute_concretes(concretes)
	# do
	# 	if concretes == null then
	# 		concretes = new ConcreteTypes
	# 	end

	# 	# For now the concrete types of self are the subclasses of the current class which are instantiated
	# 	for mclass in self_mclass.loaded_subclasses do
	# 		if mclass.loaded then concretes.add(mclass)
	# 	end

	# 	# The enclosing lp is a MMethodDef, we can restrain the concrete types of self
	# 	if lp isa MMethodDef then
	# 		for rcv in concretes do
	# 			# See if `rcv` redefines the enclosing lp and so can not be
	# 			# the self of the current class
	# 			var propdef = lp.mproperty.lookup_first_definition(sys.vm.mainmodule, rcv.intro.bound_mtype)

	# 			if propdef.to_s == "hash_collection#HashSet#add" then
	# 				print "{propdef.has_supercall}"
	# 			end

	# 			# If this different lp does not contain a super-call
	# 			if not propdef.has_supercall then concretes.remove(rcv)
	# 		end
	# 	end

	# 	# Add the class where the self-expression is
	# 	if self_mclass.abstract_loaded then concretes.add(self_mclass)

	# 	# The lp is an attribute definition, so nothing to do here

	# 	if not concretes.is_empty then
	# 		return concretes
	# 	else
	# 		return null
	# 	end
	# end
end

# MO of instantiation sites
class MONew
	super MOExpr

	# The pattern of this site
	var pattern: MONewPattern is writable, noinit

	# If any, the associated callsite of the constructor
	var callsite: nullable MOCallSite

	redef fun compute_concretes(concretes)
	do
		if concretes == null then
			concretes = new ConcreteTypes
			concretes.immutable = true # A new is imutable
		end

		# TODO: if the class is abstract do not consider concrete types,
		# we need here a patch to handle this
		if self.pattern.cls.is_abstract then
			return null
		end

		if not concretes.has(self.pattern.cls) then concretes.add(self.pattern.cls)

		return concretes
	end

	init(mpropdef: MPropDef, node: AExpr)
	do
		super(mpropdef, node)
		if not sys.vm.all_new_sites.has(self) then sys.vm.all_new_sites.add(self)
		lp = mpropdef
		lp.monews.add(self)
	end
end

# MO of super calls
class MOSuper
	super MOExpr

	init(lp: MPropDef, node: nullable AExpr)
	do
		super(lp, node)
		sys.vm.all_moentities.add(self)
		sys.vm.mo_supers.add(self)
	end
end

# MO of literals
class MOLit
	super MOExpr
end

# MO of primitives
class MOPrimitive
	super MOExpr
end

# Root hierarchy of objets sites
abstract class MOSite
	super MOEntity

	# The type of the site pattern associated to this site
	type P: MOSitePattern

	# The expression of the receiver
	var expr_recv: MOExpr is noinit, writable

	# The pattern using by this expression site
	var pattern: P is writable, noinit

	# List of concrete receivers if all receivers can be statically determined
	var concrete_receivers: nullable ConcreteTypes is noinit, writable

	# Indicate if this site can be trivially optimized, and thus is in a special category in the protocol,
	# A monomorphic site is coming from a unique new of a loaded class or typed by a final class (loaded or not)
	var is_monomorph: Bool = false is writable

	# True if the site has been executed
	var is_executed: Bool = false

	# Indicate if this site has a primitive receiver
	var is_primitive: Bool = false

	fun set_executed
	do
		is_executed = true
		pattern.is_executed = true
	end

	fun pattern_factory(rst: MType, gp: MProperty, rsc: MClass): P is abstract

	# Set the flag `is_monomorph` if needed
	fun monomorphic_analysis
	do
		# Special cases of constructors
		if self isa MOInitSite then
			var concrete = new ConcreteTypes
			concrete.immutable = true
			concrete.add(pattern.rsc)
			concrete_receivers = concrete
		end

		# If the static type is final, then it is monomorph
		if pattern.rsc.is_final then
			is_monomorph = true
			var concrete = new ConcreteTypes
			concrete.immutable = true
			concrete.add(pattern.rsc)

			concrete_receivers = concrete
		end

		# If the site is coming from a new of a loaded class
		if expr_recv isa MONew then
			if expr_recv.as(MONew).pattern.cls.is_abstract then return

			is_monomorph = true
			var concrete = new ConcreteTypes
			concrete.immutable = true

			concrete.add(expr_recv.as(MONew).pattern.cls)
			concrete_receivers = concrete
		end

		# The receiver of the site is coming from a variable with a unique loaded new in dependency
		if expr_recv isa MOSSAVar and expr_recv.as(MOSSAVar).dependency isa MONew then
			var new_class = expr_recv.as(MOSSAVar).dependency.as(MONew).pattern.cls
			# The corresponding class must be loaded
			if new_class.is_abstract then return

			is_monomorph = true
			var concrete = new ConcreteTypes
			concrete.immutable = true
			concrete.add(new_class)

			concrete_receivers = concrete
		end

		# If the site was monomorph, stores it apart from polymorph sites
		if is_monomorph then
			lp.mosites.remove(self)

			if not is_primitive then
				lp.monomorph_sites.add(self)
			end

			notify_classes
		end
	end

	fun compute_concretes_site
	do
		# Do not compute concrete_type in original preexistence
		if sys.disable_preexistence_extensions then	return

		if concrete_receivers != null then return

		var res = expr_recv.compute_concretes(null)
		if res != null then
			concrete_receivers = res

			# The classes of the concrete need to know they are used as concrete types
			notify_classes
		end
	end

	# Get concretes receivers (or return empty list)
	fun get_concretes: nullable List[MClass]
	do
		if not is_monomorph then compute_concretes_site

		return concrete_receivers
	end

	# Indicate to the class inside the concrete types that `self` used them as concretes
	fun notify_classes
	do
		for mclass in concrete_receivers do
			if not mclass.concrete_sites.has(self) then mclass.concrete_sites.add(self)
		end
	end

	init(mpropdef: MPropDef, node: AExpr)
	do
		super(mpropdef, node)

		add_entities
	end

	fun add_entities
	do
		# The receiver type
		var rcv_ast: nullable AExpr = null

		if ast isa ASendExpr then
			rcv_ast = ast.as(ASendExpr).n_expr
		else if ast isa AAttrFormExpr then
			rcv_ast = ast.as(AAttrFormExpr).n_expr
		else if ast isa AAsCastForm then
			rcv_ast = ast.as(AAsCastForm).n_expr
		else if ast isa AIsaExpr then
			rcv_ast = ast.as(AIsaExpr).n_expr
		else if ast isa ANewExpr then
			rcv_ast = ast
		else if ast isa ASuperExpr then
			rcv_ast = ast
		else
			print ast.as(not null)
		end

		if rcv_ast.mtype != null and rcv_ast.mtype.is_primitive_type then
			if not lp.primitive_sites.has(self) then lp.primitive_sites.add(self)
			sys.vm.primitive_entities.add(self)
			is_primitive = true
		else
			if not lp.mosites.has(self) then lp.mosites.add(self)
			if not sys.vm.all_moentities.has(self) then sys.vm.all_moentities.add(self)
		end
	end
end

# MO of global properties sites
abstract class MOPropSite
	super MOSite

	redef type P: MOPropSitePattern
end

# Object expression
abstract class MOExprSite
	super MOSite
	super MOExpr

	redef type P: MOExprSitePattern

	init(mpropdef: MPropDef, node: AExpr)
	do
		lp = mpropdef
		ast = node
	end
end

# MO of a subtype test site
abstract class MOSubtypeSite
	super MOExprSite

	redef type P: MOSubtypeSitePattern

	# Static type on which the test is applied
	var target: MType

	# Static MClass of the class
	var target_mclass: MClass

	var rst: MType is noinit

	init(mpropdef: MPropDef, node: AExpr, target: MType)
	do
		lp = mpropdef
		ast = node
		add_entities

		var mclass = target.get_mclass(sys.vm, mpropdef)
		self.target = mclass.mclass_type
		self.target_mclass = mclass.as(not null)
	end

	redef fun pretty_print(file)
	do
		super
		file.write("target {target}")
	end
end

class MOAsNotNullSite
	super MOExprSite

	redef type P: MOAsNotNullPattern
end

# MO of .as(Type) expr
class MOAsSubtypeSite
	super MOSubtypeSite

	# Compute concrete types returned by the cast
	redef fun compute_concretes(concretes)
	do
		if sys.disable_preexistence_extensions then return null

		var sup = super
		if sup != null then return sup

		# The candidates of the subtyping-test
		if concretes == null then concretes = new ConcreteTypes

		# If we have concrete receivers use them compute concretes types
		if concrete_receivers != null then
			# See which concretes receivers are subtypes of the target of the cast
			for rcv in concrete_receivers.as(not null) do
				if vm.is_subclass(rcv, target_mclass) then concretes.add(rcv)
			end
		else
			# We do not have concrete receivers, so the candidates are all loaded subclasses of the target
			return null
			# if target_mclass.abstract_loaded then concretes.add(target_mclass)

			# for mclass in target_mclass.loaded_subclasses do
			# 	if mclass.abstract_loaded then concretes.add(mclass)
			# end
		end

		if not concretes.is_empty then
			return concretes
		else
			return null
		end
	end

	redef init(mpropdef: MPropDef, node: AExpr, t: MType)
	do
		super(mpropdef, node, t)
	end
end

# MO of isa expr
class MOIsaSubtypeSite
	super MOSubtypeSite

	redef init(mpropdef: MPropDef, node: AExpr, t: MType)
	do
		super(mpropdef, node, t)
	end
end

# MO of attribute access
abstract class MOAttrSite
	super MOPropSite

	redef type P: MOAttrPattern

	redef init(mpropdef: MPropDef, node: AExpr)
	do
		super(mpropdef, node)

		add_entities
	end
end

redef class CallSite
	var mocallsite: nullable MOCallSite
end

# MO of method call
class MOCallSite
	super MOPropSite
	super MOExprSite

	redef type P: MOCallSitePattern

	# The corresponding CallSite object
	var callsite: CallSite

	# Values of each arguments
	var given_args = new List[MOExpr]

	# Indicate if this callsite is used as a receiver of another site
	var as_receiver = false is writable

	init(mpropdef: MPropDef, node: AExpr, cs: CallSite)
	do
		lp = mpropdef
		ast = node

		callsite = cs
		callsite.mocallsite = self

		add_entities

		# Special case for is_same_instance method
		# TODO: to remove after the end of experiments
		if cs.mproperty.name == "is_same_instance" then
			sys.vm.primitive_entities.add(self)
			is_primitive = true
		else if node isa ANewExpr then
			sys.vm.all_moentities.add(self)
		else if node.as(ASendExpr).n_expr.mtype != null and node.as(ASendExpr).n_expr.mtype.is_primitive_type then
			sys.vm.primitive_entities.add(self)
			is_primitive = true
		else
			sys.vm.all_moentities.add(self)
		end
	end

	redef fun pretty_print(file)
	do
		super
		file.write(" MOCallSite given_args = ")
		for arg in given_args do
			if arg isa MOVar then
				file.write("{arg.variable.name} ")
			else
				file.write("{arg} ")
			end
		end
	end

	fun concrete_callees: List[MMethodDef]
	do
		var callees = new List[MMethodDef]

		if is_monomorph then
			var propdef = pattern.gp.lookup_first_definition(sys.vm.mainmodule, concrete_receivers.first.intro.bound_mtype)
			callees.add(propdef)
			return callees
		end

		for rcv in concrete_receivers.as(not null) do
			if not rcv.abstract_loaded then continue

			if not rcv.intro.bound_mtype.has_mproperty(vm.mainmodule, pattern.gp) then continue

			var propdef = pattern.gp.lookup_first_definition(sys.vm.mainmodule, rcv.intro.bound_mtype)
			if not callees.has(propdef) then
				callees.add(propdef)
			end
		end

		return callees
	end
end

# A call to a method with a return
class MOFunctionSite
	super MOCallSite

	redef fun pattern_factory(rst, gp, rsc)
	do
		return (new MOCallSitePattern(rst, rsc, gp.as(MMethod), true)).init_abstract
	end

	# Compute inter-procedural concrete types
	redef fun compute_concretes(concretes)
	do
		# Concrete types of method calls are not consider in original preexistence
		if sys.disable_preexistence_extensions then return null

		var sup = super
		if sup != null then return sup

		# The set of callees of this callsite
		var callees = new List[MMethodDef]

		# If we have concrete receivers use them to get the concrete callees
		if concrete_receivers != null then
			for rcv in concrete_receivers.as(not null) do
				if not rcv.abstract_loaded then continue

				var propdef = pattern.gp.lookup_first_definition(sys.vm.mainmodule, rcv.intro.bound_mtype)
				if not callees.has(propdef) then
					callees.add(propdef)
				end
			end
		else
			callees = pattern.callees
		end

		# The concrete types of this callsite is the union of concrete types of all callees
		var concrete_types = new ConcreteTypes
		concrete_types.immutable = false

		for callee in callees do
			var return_concretes = callee.compute_concretes(sys.vm)

			# The return must have immutable concrete types to be considered
			if return_concretes != null and return_concretes.immutable then
				concrete_types.add_all(return_concretes)
			else
				return null
			end
		end

		if not concrete_types.is_empty then
			return concrete_types
		else
			return null
		end
	end
end

# A call to a method which has no return
class MOProcedureSite
	super MOCallSite

	redef fun pattern_factory(rst, gp, rsc)
	do
		return (new MOCallSitePattern(rst, rsc, gp.as(MMethod), false)).init_abstract
	end
end

# A call to an initializer
class MOInitSite
	super MOProcedureSite

	# A call to an initializer is always static
	redef var is_monomorph = true
end

# MO of read attribute
class MOReadSite
	super MOExprSite
	super MOAttrSite

	redef init(mpropdef: MPropDef, node: AExpr)
	do
		super
		add_entities
	end

	redef type P: MOReadSitePattern

	redef fun pattern_factory(rst, gp, rsc)
	do
		return (new MOReadSitePattern(rst, rsc, gp.as(MAttribute))).init_abstract
	end

	# Tell if the attribute is immutable, useless at the moment
	var immutable = false

	redef fun compute_concretes(concretes: nullable ConcreteTypes): nullable ConcreteTypes
	do
		var sup = super
		if sup != null then return sup

		# Compute the global (closed-world) concrete types of this attribute
		if pattern.gp.has_concrete_types then
			if concretes == null then
				concretes = new ConcreteTypes
				concretes.immutable = true
			end

			concretes.add_all(pattern.gp.compute_concretes)

			if not concretes.is_empty then return concretes
		end

		return null
	end
end

# MO of write attribute
class MOWriteSite
	super MOAttrSite

	redef type P: MOWriteSitePattern

	redef init(mpropdef: MPropDef, node: AExpr)
	do
		super(mpropdef, node)
		add_entities
	end

	redef fun pattern_factory(rst, gp, rsc)
	do
		return (new MOWriteSitePattern(rst, rsc, gp.as(MAttribute))).init_abstract
	end
end

# MO of null
class MONull
	super MOLit
end

redef class MClass
	# List of patterns of MOPropSite
	var sites_patterns = new List[MOPropSitePattern]

	# Pattern of MONew of self
	var new_pattern: MONewPattern = new MONewPattern(self)

	# List of patterns of subtypes test
	var subtype_pattern = new List[MOSubtypeSitePattern]

	# List of subtype patterns for which self is the target
	var subtype_target_patterns = new List[MOSubtypeSitePattern]

	# The only asnotnull pattern
	var asnotnull_pattern: nullable MOAsNotNullPattern

	# Contrary relation of concrete_receivers, the sites in which self appears as a concrete
	var concrete_sites = new List[MOSite]

	# The list of all self_expressions on which self
	var self_sites = new List[MOSelf]

	# The list of PICPatterns of this class,
	# this class is considered the Property Introduction Class
	# and stores alls the PICPatterns for a property which is introduced in self
	var pic_patterns = new List[PICPattern]

	# `self` is an instance of object
	fun is_instance_of_object(vm: VirtualMachine): Bool
	do
		return self.in_hierarchy(vm.mainmodule).greaters.length == 1
	end

	# Create (if not exists) and set a pattern for object subtype sites
	fun set_asnotnull_pattern(site: MOAsNotNullSite, mpropdef: MPropDef): MOAsNotNullPattern
	do
		if asnotnull_pattern == null then
			asnotnull_pattern = (new MOAsNotNullPattern(mclass_type, mclass_type.get_mclass(sys.vm, mpropdef).as(not null))).init_abstract
		end

		site.pattern = asnotnull_pattern.as(not null)
		return asnotnull_pattern.as(not null)
	end

	fun set_subtype_pattern(site: MOSubtypeSite, mpropdef: MPropDef)
	do
		var pattern: nullable MOSubtypeSitePattern = null

		for p in subtype_pattern do
			if p.rsc == self and p.target == site.target then
				pattern = p
				break
			end
		end

		if pattern == null then
			pattern = (new MOSubtypeSitePattern(mclass_type, mclass_type.get_mclass(sys.vm, mpropdef).as(not null), site.target, site.target_mclass)).init_abstract
			subtype_pattern.add(pattern)
		end

		pattern.add_site(site)

		# Add the pattern to `subtype_target_patterns`
		if not site.target_mclass.subtype_target_patterns.has(pattern) then
			site.target_mclass.subtype_target_patterns.add(pattern)
		end
	end

	# Create (if not exists) and set a pattern for objet prop sites
	fun set_site_pattern(site: MOPropSite, gp: MProperty)
	do
		var pattern: nullable MOPropSitePattern = null

		for p in sites_patterns do
			if p.gp == gp and p.rsc == self and p.compatible_site(site) then
				assert p.rsc == self
				pattern = p
				break
			end
		end

		if pattern == null then
			pattern = site.pattern_factory(mclass_type, gp, self)
			sites_patterns.add(pattern)
		end

		pattern.add_site(site)
	end

	# Add newsite expression in the NewPattern associated to this class
	fun set_new_pattern(newsite: MONew)
	do
		new_pattern.newexprs.add(newsite)
		newsite.pattern = new_pattern
	end

	# Update the concrete types of self sites of this class
	fun update_self_sites
	do
		for self_site in self_sites do
			self_site.compute_concretes(null)
		end
	end
end

redef class VirtualMachine
	# All compiled MPropDef
	var compiled_mproperties = new List[MPropDef]

	# All living global methods
	var compiled_global_methods = new List[MMethod]

	# All living new sites
	var all_new_sites = new List[MONew]

	# The list of all object entities
	var all_moexprs = new List[MOExpr]

	# The list of all object entities
	var all_moentities = new HashSet[MOEntity]

	# Primitive entities of the model (callsites with a primitive receiver...)
	var primitive_entities = new HashSet[MOEntity]

	# The list of all MOSuper
	var mo_supers = new List[MOSuper]

	# All patterns of the program
	var all_patterns = new List[MOSitePattern]

	# All PICPatterns of the program
	var all_picpatterns = new List[PICPattern]

	# All MONewPattern
	var all_new_patterns = new List[MONewPattern]
end

redef class MType
	# The artificial class of the null type
	var null_class: nullable MClass

	# True if self is a primitive type
	fun is_primitive_type: Bool
	do
		if name == "Discrete" or name == "nullable Discrete" then return true
		if name == "Numeric" or name == "nullable Numeric" then return true
		if name == "Bool" or name == "nullable Bool" then return true
		if name == "Int" or name == "nullable Int" then return true
		if name == "Char" or name == "nullable Char" then return true

		return false
	end

	# Get the class of the type
	fun get_mclass(vm: VirtualMachine, mpropdef: MPropDef): nullable MClass
	do
		if self isa MNullType then
			if null_class == null then
				null_class = new MClass(vm.mainmodule, "Null", null, concrete_kind, public_visibility)
			end
			return null_class.as(not null)
		else if self isa MNotNullType then
			return self.mtype.get_mclass(vm, mpropdef)
		else if self isa MClassType then
			return self.mclass
		else if self isa MNullableType then
			return self.mtype.get_mclass(vm, mpropdef)
		else if self isa MFormalType then

			var anchor: MType = mpropdef.mclassdef.bound_mtype
			var res = anchor_to(vm.mainmodule, anchor.as(MClassType)).get_mclass(vm, mpropdef)

			return res
		else
			# NYI
			abort
		end
	end
end

redef class ANode
	fun get_receiver: AExpr is abstract
end

redef class AExpr
	# Clone a AST expression to a MOEntity
	# `mpropdef` is the local property containing this expression (or expression-site)
	fun ast2mo(mpropdef: MPropDef): MOEntity is abstract

	fun copy_site(mpropdef: MPropDef): MOEntity is abstract

	# The corresponding model entity
	var mo_entity: nullable MOEntity
end

redef class AAttrFormExpr
	redef fun get_receiver
	do
		return n_expr
	end

	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var attr_site = copy_site(mpropdef).as(MOAttrSite)

		# Associate the MOEntity with the AST node
		mo_entity = attr_site

		var recv = get_receiver
		attr_site.expr_recv = recv.ast2mo(mpropdef).as(MOExpr)

		var recv_class = recv.mtype.as(not null).get_mclass(vm, mpropdef).as(not null)
		recv_class.set_site_pattern(attr_site, mproperty.as(not null))

		return attr_site
	end
end

redef class AAttrExpr
	redef fun copy_site(mpropdef: MPropDef): MOReadSite
	do
		return new MOReadSite(mpropdef, self)
	end
end

redef class AAttrAssignExpr
	redef fun copy_site(mpropdef: MPropDef): MOWriteSite
	do
		return new MOWriteSite(mpropdef, self)
	end
end

redef class AAttrReassignExpr
	redef fun copy_site(mpropdef: MPropDef): MOWriteSite
	do
		return new MOWriteSite(mpropdef, self)
	end
end

redef class AIssetAttrExpr
	redef fun copy_site(mpropdef: MPropDef): MOReadSite
	do
		return new MOReadSite(mpropdef, self)
	end
end

class ASubtypeExpr
	super AExpr

	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var recv = get_receiver
		var cast_site = copy_site(mpropdef).as(MOSubtypeSite)
		mo_entity = cast_site

		cast_site.expr_recv = recv.ast2mo(mpropdef).as(MOExpr)
		cast_site.rst = recv.mtype.as(not null)

		var recv_class = recv.mtype.as(not null).get_mclass(vm, mpropdef).as(not null)
		recv_class.set_subtype_pattern(cast_site, mpropdef)

		return cast_site
	end
end

redef class AIsaExpr
	super ASubtypeExpr

	redef fun get_receiver
	do
		return n_expr
	end

	redef fun copy_site(mpropdef: MPropDef): MOIsaSubtypeSite
	do
		return new MOIsaSubtypeSite(mpropdef, self, cast_type.as(not null))
	end
end

redef class AAsCastForm
	super ASubtypeExpr

	redef fun get_receiver
	do
		return n_expr
	end
end

redef class AAsCastExpr
	redef fun copy_site(mpropdef: MPropDef): MOAsSubtypeSite
	do
		return new MOAsSubtypeSite(mpropdef, self, n_type.mtype.as(not null))
	end
end

redef class AAsNotnullExpr
	redef fun copy_site(mpropdef: MPropDef): MOAsNotNullSite
	do
		return new MOAsNotNullSite(mpropdef, self)
	end

	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var moexpr = copy_site(mpropdef)
		mo_entity = moexpr

		moexpr.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)

		var recv_class = n_expr.mtype.as(not null).get_mclass(vm, mpropdef).as(not null)
		recv_class.set_asnotnull_pattern(moexpr, mpropdef)

		return moexpr
	end
end

redef class Variable
	# The associated MOVar
	var movar: nullable MOVar

	# Create the movar corresponding to this Variable, and return it
	# `mpropdef` The enclosing MPropdef
	fun get_movar(mpropdef: MPropDef): MOVar
	do
		if movar != null then return movar.as(not null)

		# The corresponding movar
		if dep_exprs.length == 0 and parameter then
			var moparam = new MOParam(mpropdef, null)

			movar = moparam
			return moparam
		else if dep_exprs.length == 1 or dep_exprs.length == 0 then
			var mossa = new MOSSAVar(mpropdef, null)
			movar = mossa

			if dep_exprs.length == 0 then
				mossa.dependency = sys.monull
			else
				mossa.dependency = dep_exprs.first.ast2mo(mpropdef).as(MOExpr)
			end

			return mossa
		else
			var mophi = new MOPhiVar(mpropdef, null)
			movar = mophi

			for dep in dep_exprs do
				mophi.dependencies.add(dep.ast2mo(mpropdef).as(MOExpr))
			end
			return mophi
		end
	end
end

redef class ANewExpr
	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var monew = new MONew(mpropdef, self)
		mpropdef.monews.add(monew)
		monew.ast = self

		mo_entity = monew

		recvtype.as(not null).mclass.set_new_pattern(monew)

		# Creation of the MOCallSite
		if callsite != null then
			var cs = callsite.as(not null)
			var recv_class = cs.recv.get_mclass(vm, mpropdef).as(not null)
			var mocallsite = new MOInitSite(mpropdef, self, cs)

			recv_class.set_site_pattern(mocallsite, cs.mproperty)

			# Association of the receiver with the new callsite
			mocallsite.expr_recv = monew

			for arg in n_args.n_exprs do
				mocallsite.given_args.add(arg.ast2mo(mpropdef).as(MOExpr))
			end

			# Associate the monew with the callsite
			monew.callsite = mocallsite
		end

		# If the option `improve_loading` is set, load the corresponding class is the new is toplevel
		if sys.improve_loading then

			# If the new is unconditionnal (i.e. at the toplevel of the enclosing method),
			# load its corresponding class if needed
			if self.block.is_unconditionnal then
				# vm.load_class(recvtype.as(not null).mclass)
				mpropdef.to_load.add(recvtype.as(not null).mclass)
			end
		end

		return monew
	end

	redef fun get_receiver
	do
		return self
	end
end

redef class ASelfExpr
	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var	movar
		if self isa AImplicitSelfExpr and self.is_sys then
			movar = new MOParam(mpropdef, null)
		else
			movar = new MOSelf(mpropdef, self, variable.as(not null), 0)
		end

		mo_entity = movar

		return movar
	end
end

redef class AVarExpr
	redef fun ast2mo(mpropdef)
	do
		return variable.as(not null).get_movar(mpropdef)
	end
end

redef class APropdef
	# Compute the implementation of sites of this local property when the AST node is compiled
	redef fun compile(vm)
	do
		super

		# Compile all object-mechanisms sites
		for site in object_sites do
			site.ast2mo(mpropdef.as(not null))
		end

		# Transform all Variable into MOVar
		mpropdef.variables = new Array[MOVar]
		for variable in variables do
			var movar = variable.get_movar(mpropdef.as(not null))
			mpropdef.variables.add(movar)
		end

		mpropdef.return_expr = returnvar.get_movar(mpropdef.as(not null))

		mpropdef.compile_mo
	end
end

redef class ASendExpr

	fun copy_site_accessor(mpropdef: MPropDef, called_node_ast: AAttrPropdef): MOAttrSite
	do
		var moattr: MOAttrSite
		var params_len = callsite.as(not null).msignature.mparameters.length

		if params_len == 0 then
			# The node is a MOReadSite
			moattr = new MOReadSite(mpropdef, self)
		else
			# The node is a MOWriteSite
			assert params_len == 1
			moattr = new MOWriteSite(mpropdef, self)
		end

		var recv_class = n_expr.mtype.as(not null).get_mclass(vm, mpropdef).as(not null)

		recv_class.set_site_pattern(moattr, called_node_ast.mpropdef.as(not null).mproperty)

		return moattr
	end

	fun copy_site_method(mpropdef: MPropDef): MOCallSite
	do
		var cs = callsite.as(not null)
		var recv_class = cs.recv.get_mclass(vm, mpropdef).as(not null)

		# If the receiver is the null type, do a special treatment
		if cs.recv.to_s == "null" then
			var mocallsite = new MOProcedureSite(mpropdef, self, cs)

			# Do not create a pattern for these callsites
			recv_class.set_site_pattern(mocallsite, cs.mproperty)
			return mocallsite
		else
			# Test if the return type of the introduction property is a primitive
			var primitive_return = false
			if cs.mpropdef.msignature.return_mtype != null then
				primitive_return = cs.mpropdef.mproperty.intro.msignature.return_mtype.is_primitive_type
			end

			var mocallsite: MOCallSite
			if cs.mpropdef.msignature.return_mtype != null and not primitive_return then
				# The mproperty is a function
				mocallsite = new MOFunctionSite(mpropdef, self, cs)
			else
				# The mproperty is a procedure
				mocallsite = new MOProcedureSite(mpropdef, self, cs)
			end

			recv_class.set_site_pattern(mocallsite, cs.mproperty)

			return mocallsite
		end
	end

	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		if callsite == null then
			return sys.monull
		end

		var cs = callsite.as(not null)

		# Static dispatch with global model to known if we handle method call of attribute access
		var called_node_ast = vm.modelbuilder.mpropdef2node(cs.mpropdef)
		var is_attribute = called_node_ast isa AAttrPropdef

		if is_attribute and not cs.mproperty.mpropdefs.length > 1 then
			var mo = ast2mo_accessor(mpropdef, called_node_ast.as(AAttrPropdef))
			return mo
		else
			var mo = ast2mo_method(mpropdef, called_node_ast.as(not null), is_attribute)
			return mo
		end
	end

	# Attribute access (with method call simulation: "foo.attr" instead on "foo._attr")
	fun ast2mo_accessor(mpropdef: MPropDef, called_node_ast: AAttrPropdef): MOEntity
	do
		var moattr = copy_site_accessor(mpropdef, called_node_ast)
		mo_entity = moattr

		moattr.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)

		return moattr
	end

	# Real method call, and accessors with redefinitions
	# is_attribute is used only for stats (to know if it's a method call because of a redefinition of a attribute)
	fun ast2mo_method(mpropdef: MPropDef, called_node_ast: ANode, is_attribute: Bool): MOEntity
	do
		var mocallsite = copy_site_method(mpropdef)
		mo_entity = mocallsite

		mocallsite.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)

		# Expressions arguments given to the method called
		for arg in raw_arguments do
			mocallsite.given_args.add(arg.ast2mo(mpropdef).as(MOExpr))
		end

		return mocallsite
	end

	redef fun get_receiver
	do
		return n_expr
	end
end

redef class AParExpr
	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var moexpr = n_expr.ast2mo(mpropdef)

		mo_entity = moexpr
		return moexpr
	end
end

redef class AOnceExpr
	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var moexpr = n_expr.ast2mo(mpropdef)
		mo_entity = moexpr
		return moexpr
	end
end

redef class ASuperExpr
	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var mosuper = new MOSuper(mpropdef, self)

		mo_entity = mosuper
		return mosuper
	end
end

redef class AIfexprExpr
	redef fun ast2mo(mpropdef)
	do
		return n_expr.ast2mo(mpropdef)
	end
end

redef class AVarargExpr
	redef fun ast2mo(mpropdef)
	do
		return n_expr.ast2mo(mpropdef)
	end
end

redef class ANamedargExpr
	redef fun ast2mo(mpropdef)
	do
		return n_expr.ast2mo(mpropdef)
	end
end

redef class ARangeExpr
	# TODO: not perfect, find a better way to do this
	redef fun ast2mo(mpropdef)
	do
		return n_expr.ast2mo(mpropdef)
	end
end

redef class ANullExpr
	redef fun ast2mo(mpropdef) do return sys.monull
end

redef class AStringExpr
	redef fun ast2mo(mpropdef) do return sys.moprimitive
end

redef class ASuperstringExpr
	redef fun ast2mo(mpropdef) do return sys.moprimitive
end

redef class ACharExpr
	redef fun ast2mo(mpropdef) do return sys.moprimitive
end

redef class AIntegerExpr
	redef fun ast2mo(mpropdef) do return sys.moprimitive
end

redef class AFloatExpr
	redef fun ast2mo(mpropdef) do return sys.moprimitive
end

redef class ABoolExpr
	redef fun ast2mo(mpropdef) do return sys.moprimitive
end

redef class AArrayExpr
	redef fun ast2mo(mpropdef) do return sys.moliteral
end
