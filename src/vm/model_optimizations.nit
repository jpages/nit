# Intermediate representation of nit program running inside the VM
module model_optimizations

import compilation

redef class ToolContext
	# Enable traces of analysis
	var trace_on = new OptionBool("Display the trace of model optimizing / preexistence analysis", "--mo-trace")

	redef init
	do
		super
		option_context.add_option(trace_on)
	end
end

redef class Sys
	# Display trace if --mo-trace is set
	fun trace(buf: String) do if trace_on then print(buf)

	# Tell if trace is enabled
	var trace_on: Bool is noinit

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
		super(mainmodule, arguments)
	end
end

# Pattern of instantiation sites
class MONewPattern
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

	fun init_abstract: SELF
	do
		sys.vm.all_patterns.add(self)
		return self
	end

	# Add a site
	fun add_site(site: S)
	do
		assert not sites.has(site)

		sites.add(site)
		site.pattern = self
	end

	fun trace: String
	do
		return "{rst.name} {rsc.name} "
	end
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

	# Candidates local properties owning by the GP
	var callees = new List[LP]

	# Number of calls on uncompiled methods
	var cuc = 0

	#TODO: contructeur qui doit gérer l'association GP <-> Pattern
	init
	do
		super
		gp.patterns.add(self)
	end

	fun compatible_site(site: MOPropSite): Bool is abstract

	redef fun trace
	do
		return super + "{gp} {gp.name} "
	end
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

	redef fun trace
	do
		return super + "target = {target} {target.name}"
	end
end

class MOAsNotNullPattern
	super MOExprSitePattern

	redef type S: MOAsNotNullSite
end

# Pattern of method call
class MOCallSitePattern
	super MOExprSitePattern
	super MOPropSitePattern

	redef type GP: MMethod

	redef type LP: MMethodDef

	redef type S: MOCallSite

	init(rst: MType, rsc: MClass, gp: MMethod)
	do
		super(rst, rsc, gp)

		self.gp = gp
		self.rst = rst
		self.rsc = rsc

		if rsc.abstract_loaded then
			for subclass in rsc.loaded_subclasses do
				var lp_rsc = gp.lookup_first_definition(sys.vm.mainmodule, subclass.intro.bound_mtype)

				if not gp.living_mpropdefs.has(lp_rsc) then
					gp.living_mpropdefs.add(lp_rsc)
				end

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
		if not callees.has(mpropdef) then
			callees.add(mpropdef)
			mpropdef.callers.add(self)

			# If the mpropdef is abstract do not count it in uncompiled methods
			if not mpropdef.is_abstract and not mpropdef.is_compiled then cuc += 1
		end
	end
end

# Common subpattern of all attributes (read/write)
abstract class MOAttrPattern
	super MOPropSitePattern

	redef type GP: MAttribute

	redef type LP: MAttributeDef
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

	# Compile the property
	fun compile_mo
	do
		sys.vm.compiled_mproperties.add(self)

		for pattern in callers do
			pattern.cuc -= 1
		end

		# if mclassdef.mclass.concrete_caller_sites != null then
		# 	for site in mclassdef.mclass.concrete_caller_sites do

		# 	end
		# end

		is_compiled = true

		for site in mosites do
			# Init the concrete receivers
			site.compute_concretes
		end
	end

	# Return expression of the propdef (null if procedure)
	var return_expr: nullable MOVar is noinit, writable

	# An object is never return if return_expr is not a MOVar
	fun return_expr_is_object: Bool do return return_expr isa MOVar

	# List of instantiations sites in this local property
	var monews = new List[MONew]

	# List of object sites in this local property
	var mosites = new List[MOSite]

	# All MOVar inside the mpropdef, including self and returnvar
	var variables: Array[MOVar] = new Array[MOVar]
end

redef class MMethod
	redef type LP: MMethodDef

	redef type PATTERN: MOCallSitePattern

	redef fun add_propdef(mpropdef)
	do
		super

		for pattern in patterns do
			pattern.add_lp(mpropdef)
		end
	end
end

redef class MMethodDef
	redef type P: MOCallSitePattern
end

# Root hierarchy of MO entities
abstract class MOEntity

	# The local property containing this expression
	var lp: MPropDef

	fun pretty_print(file: FileWriter)
	do
	end
end

# Root hierarchy of expressions
abstract class MOExpr
	super MOEntity

	init
	do
		sys.vm.all_moexprs.add(self)
	end

	fun compute_concretes(concretes: nullable List[MClass]): nullable List[MClass]
	do
		# By default, an expression has not concretes
		return null
	end
end

# MO of variables
abstract class MOVar
	super MOExpr

	# The Variable objet refered by this node
	var variable: Variable

	# The offset of the variable in it environment, or the position of parameter
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
		return dependency.compute_concretes(concretes)
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
		for dep in dependencies do
			concretes = dep.compute_concretes(concretes)

			# All dependencies must be concrete (from a new)
			if concretes == null then return null
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

# MO of instantiation sites
class MONew
	super MOExpr

	# The pattern of this site
	var pattern: MONewPattern is writable, noinit

	redef fun compute_concretes(concretes)
	do
		if concretes == null then
			concretes = new List[MClass]
		end

		if not concretes.has(self.pattern.cls) then concretes.add(self.pattern.cls)

		return concretes
	end

	init(mpropdef: MPropDef)
	do
		sys.vm.all_new_sites.add(self)
		lp = mpropdef
		lp.monews.add(self)
	end
end

# MO of super calls
class MOSuper
	super MOExpr

	init
	do
		sys.vm.all_moentitites.add(self)
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

	# The AST node where this site comes from
	var ast: AExpr

	# The type of the site pattern associated to this site
	type P: MOSitePattern

	# The expression of the receiver
	var expr_recv: MOExpr is noinit, writable

	# The pattern using by this expression site
	var pattern: P is writable, noinit

	# List of concretes receivers if ALL receivers can be statically and with intra-procedural analysis determined
	var concretes_receivers: nullable List[MClass] is noinit, writable

	# True if the site has been executed
	var is_executed: Bool = false

	fun set_executed
	do
		is_executed = true
		pattern.is_executed = true
	end

	fun pattern_factory(rst: MType, gp: MProperty, rsc: MClass): P is abstract

	private fun compute_concretes
	do
		var res = expr_recv.compute_concretes(null)
		if res != null then
			concretes_receivers = res

			# for concrete in res do
			# 	if concrete.concrete_caller_sites == null then
			# 		concrete.concrete_caller_sites = new List[MOSite]
			# 	end

			# 	concrete.concrete_caller_sites.add(self)
			# end
		end
	end

	# Get concretes receivers (or return empty list)
	fun get_concretes: nullable List[MClass]
	do
		return concretes_receivers
	end

	init(ast: AExpr, mpropdef: MPropDef)
	do
		super(mpropdef)
		self.ast = ast
		lp = mpropdef
		lp.mosites.add(self)

		sys.vm.all_moentitites.add(self)
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

	init(ast: AExpr, mpropdef: MPropDef, target: MType)
	do
		super
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

# MO of global properties sites
abstract class MOPropSite
	super MOSite

	redef type P: MOPropSitePattern
end

# MO of object expression
abstract class MOExprSite
	# super MOPropSite
	super MOSite
	super MOExpr

	redef type P: MOExprSitePattern
end

class MOAsNotNullSite
	super MOExprSite

	redef type P: MOAsNotNullPattern
end

# MO of .as(Type) expr
class MOAsSubtypeSite
	super MOSubtypeSite
end

# MO of isa expr
class MOIsaSubtypeSite
	super MOSubtypeSite
end

# MO of attribute access
abstract class MOAttrSite
	super MOPropSite

	redef type P: MOAttrPattern
end

# MO of method call
class MOCallSite
	super MOPropSite
	super MOExprSite

	redef type P: MOCallSitePattern

	# Values of each arguments
	var given_args = new List[MOExpr]

	redef fun pattern_factory(rst, gp, rsc)
	do
		return (new MOCallSitePattern(rst, rsc, gp.as(MMethod))).init_abstract
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

	fun concretes_callees: List[MPropDef]
	do
		var callees = new List[MPropDef]

		for rcv in concretes_receivers.as(not null) do
			var propdef = pattern.gp.lookup_first_definition(sys.vm.mainmodule, rcv.intro.bound_mtype)

			if not callees.has(propdef) then
				callees.add(propdef)
			end
		end

		return callees
	end

	redef fun set_executed
	do
		if is_executed == false then
			if pattern.callees.length == 0 then
				# print "Pattern without callees, pattern.gp {pattern.gp} pattern.rsc {pattern.rsc} {pattern.gp.living_mpropdefs}"
			end
		end

		super
	end
end

# MO of read attribute
class MOReadSite
	super MOExprSite
	super MOAttrSite

	redef type P: MOReadSitePattern

	redef fun pattern_factory(rst, gp, rsc)
	do
		return (new MOReadSitePattern(rst, rsc, gp.as(MAttribute))).init_abstract
	end

	# Tell if the attribute is immutable, useless at the moment
	var immutable = false
end

# MO of write attribute
class MOWriteSite
	super MOAttrSite

	redef type P: MOWriteSitePattern

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
	#TODO: to debug
	var sites_patterns = new List[MOPropSitePattern]

	# Pattern of MONew of self
	var new_pattern: MONewPattern = new MONewPattern(self)

	# List of patterns of subtypes test
	var subtype_pattern = new List[MOSubtypeSitePattern]

	# The only asnotnull pattern
	var asnotnull_pattern: nullable MOAsNotNullPattern

	# Contrary relation of concretes_receivers
	var concrete_caller_sites: nullable List[MOSite]

	# `self` is an instance of object
	fun is_instance_of_object(vm:VirtualMachine): Bool
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

	# Add newsite expression in the NewPattern assocociated to this class
	fun set_new_pattern(newsite: MONew)
	do
		new_pattern.newexprs.add(newsite)
		newsite.pattern = new_pattern
	end

	# Indicate if target is the only loaded subclass of target
	fun single_loaded_subclass(target: MClass): Bool
	do
		if self == target and subclasses.length == 0 then
			return true
		else if subclasses.length == 1 then
			return subclasses.first.single_loaded_subclass(target)
		end

		return false
	end
end

redef class VirtualMachine
	# All living MPropDef
	var compiled_mproperties = new List[MPropDef]

	# All living new sites
	var all_new_sites = new List[MONew]

	# The list of all object entities
	var all_moexprs = new List[MOExpr]

	# The list of all object entities
	var all_moentitites = new List[MOEntity]

	# The list of all MOSuper
	var mo_supers = new List[MOSuper]

	# All patterns of the program
	var all_patterns = new List[MOSitePattern]

	# All MONewPattern
	var all_new_patterns = new List[MONewPattern]

	redef fun load_class(mclass)
	do
		super

		# For all superclasses (including self)
		for superclass in mclass.ordering do
			for pattern in superclass.sites_patterns do
				# We only update callsite patterns
				if not pattern isa MOCallSitePattern then continue

				var lp_rsc = pattern.gp.lookup_first_definition(sys.vm.mainmodule, pattern.rsc.intro.bound_mtype)

				if not pattern.gp.living_mpropdefs.has(lp_rsc) then
					pattern.gp.living_mpropdefs.add(lp_rsc)
				end

				pattern.add_lp(lp_rsc)
			end
		end
	end
end

redef class MType
	# True if self is a primitive type
	fun is_primitive_type: Bool
	do
		if self.to_s == "Int" then return true
		if self.to_s == "nullable Int" then return true
		if self.to_s == "Char" then return true
		if self.to_s == "nullable Char" then return true
		if self.to_s == "Bool" then return true
		return false
	end

	# Get the class of the type
	fun get_mclass(vm: VirtualMachine, mpropdef: MPropDef): nullable MClass
	do
		if self isa MNullType then
			return null
		else if self isa MNotNullType then
			return self.mtype.get_mclass(vm, mpropdef)
		else if self isa MClassType then
			return self.mclass
		else if self isa MNullableType then
			return self.mtype.get_mclass(vm, mpropdef)
		else if self isa MFormalType then

			var anchor: MType = mpropdef.mclassdef.bound_mtype
			var res = anchor_to(sys.vm.mainmodule, anchor.as(MClassType)).get_mclass(vm, mpropdef)

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

		var recv = get_receiver
		attr_site.expr_recv = recv.ast2mo(mpropdef).as(MOExpr)

		var recv_class = recv.mtype.as(not null).get_mclass(vm, mpropdef).as(not null)
		recv_class.set_site_pattern(attr_site, mproperty.as(not null))

		# Associate the MOEntity with the AST node
		mo_entity = attr_site

		return attr_site
	end
end

redef class AAttrExpr
	redef fun copy_site(mpropdef: MPropDef): MOReadSite
	do
		return new MOReadSite(self, mpropdef)
	end
end

redef class AAttrAssignExpr
	redef fun copy_site(mpropdef: MPropDef): MOWriteSite
	do
		return new MOWriteSite(self, mpropdef)
	end
end

redef class AAttrReassignExpr
	redef fun copy_site(mpropdef: MPropDef): MOWriteSite
	do
		return new MOWriteSite(self, mpropdef)
	end
end

redef class AIssetAttrExpr
	redef fun copy_site(mpropdef: MPropDef): MOReadSite
	do
		return new MOReadSite(self, mpropdef)
	end
end

class ASubtypeExpr
	super AExpr

	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var recv = get_receiver
		var cast_site = copy_site(mpropdef).as(MOSubtypeSite)
		cast_site.expr_recv = recv.ast2mo(mpropdef).as(MOExpr)

		var recv_class = recv.mtype.as(not null).get_mclass(vm, mpropdef).as(not null)
		recv_class.set_subtype_pattern(cast_site, mpropdef)

		mo_entity = cast_site
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
		return new MOIsaSubtypeSite(self, mpropdef, cast_type.as(not null))
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
		return new MOAsSubtypeSite(self, mpropdef, n_type.mtype.as(not null))
	end
end

redef class AAsNotnullExpr
	redef fun copy_site(mpropdef: MPropDef): MOAsNotNullSite
	do
		return new MOAsNotNullSite(self, mpropdef)
	end

	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var moexpr = copy_site(mpropdef)
		moexpr.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)

		var recv_class = n_expr.mtype.as(not null).get_mclass(vm, mpropdef).as(not null)
		recv_class.set_asnotnull_pattern(moexpr, mpropdef)

		mo_entity = moexpr
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
			var moparam = new MOParam(mpropdef, self, position)

			movar = moparam
			return moparam
		else if dep_exprs.length == 1 or dep_exprs.length == 0 then
			var mossa = new MOSSAVar(mpropdef, self, position)
			movar = mossa

			if dep_exprs.length == 0 then
				mossa.dependency = sys.monull
			else
				mossa.dependency = dep_exprs.first.ast2mo(mpropdef).as(MOExpr)
			end

			return mossa
		else
			var mophi = new MOPhiVar(mpropdef, self, position)
			movar = mophi

			for dep in dep_exprs do mophi.dependencies.add(dep.ast2mo(mpropdef).as(MOExpr))

			return mophi
		end
	end
end

redef class ANewExpr
	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var monew = new MONew(mpropdef)
		mpropdef.monews.add(monew)
		recvtype.as(not null).mclass.set_new_pattern(monew)

		mo_entity = monew
		return monew
	end
end

redef class ASelfExpr
	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var movar = new MOParam(mpropdef, variable.as(not null), 0)

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
			moattr = new MOReadSite(self, mpropdef)
		else
			# The node is a MOWriteSite
			assert params_len == 1
			moattr = new MOWriteSite(self, mpropdef)
		end

		var recv_class = n_expr.mtype.as(not null).get_mclass(vm, mpropdef).as(not null)
		recv_class.set_site_pattern(moattr, called_node_ast.mpropdef.as(not null).mproperty)

		return moattr
	end

	fun copy_site_method(mpropdef: MPropDef): MOCallSite
	do
		var cs = callsite.as(not null)
		var recv_class = cs.recv.get_mclass(vm, mpropdef).as(not null)
		var mocallsite = new MOCallSite(self, mpropdef)

		recv_class.set_site_pattern(mocallsite, cs.mproperty)

		return mocallsite
	end

	redef fun ast2mo(mpropdef)
	do
		if mo_entity != null then return mo_entity.as(not null)

		var cs = callsite.as(not null)

		# Static dispatch with global model to known if we handle method call of attribute access
		var called_node_ast = vm.modelbuilder.mpropdef2node(cs.mpropdef)
		var is_attribute = called_node_ast isa AAttrPropdef

		if is_attribute and not cs.mproperty.mpropdefs.length > 1 then
			var mo = ast2mo_accessor(mpropdef, called_node_ast.as(AAttrPropdef))
			mo_entity = mo
			return mo
		else
			var mo = ast2mo_method(mpropdef, called_node_ast.as(not null), is_attribute)
			mo_entity = mo
			return mo
		end
	end

	# Attribute access (with method call simulation: "foo.attr" instead on "foo._attr")
	fun ast2mo_accessor(mpropdef: MPropDef, called_node_ast: AAttrPropdef): MOEntity
	do
		var moattr = copy_site_accessor(mpropdef, called_node_ast)

		moattr.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)

		return moattr
	end

	# Real method call, and accessors with redefinitions
	# is_attribute is used only for stats (to kwon if it's a method call because of a redefinition of a attribute)
	fun ast2mo_method(mpropdef: MPropDef, called_node_ast: ANode, is_attribute: Bool): MOEntity
	do
		var mocallsite = copy_site_method(mpropdef)

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

		var mosuper = new MOSuper(mpropdef)

		mo_entity = mosuper
		return mosuper
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

redef class AIntExpr
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
