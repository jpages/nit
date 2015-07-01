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

	# Hashmap used for clone AST to MO
	# The key is typed by ANode instead of AExpr, because we use get_movar to get the return expression of a method,
	# and get_movar needs to use this table to put the generated MOExpr.
	var ast2mo_clone_table = new HashMap[ANode, MOEntity]

	var var2mo_clone_table = new HashMap[Variable, MOVar]

	# Singleton of MONull
	var monull = new MONull is lazy

	# Singleton of MOPrimitive
	var moprimitive = new MOPrimitive is lazy

	# Singleton of MOLiteral
	var moliteral = new MOLit is lazy
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

	# List of expressions that refers to this pattern
	var sites = new List[S]

	# Add a site
	fun add_site(site: S)
	do
		assert not sites.has(site)

		sites.add(site)
		site.pattern = self
	end
end

# Pattern of subtype test sites
class MOSubtypeSitePattern
	super MOExprSitePattern

	redef type S: MOSubtypeSite

	# Static type of the target
	var target: MType
end

class MOAsNotNullPattern
	super MOExprSitePattern

	redef type S: MOAsNotNullSite
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

	# Add a new method on this pattern
	fun add_lp(mpropdef: LP)
	do
		callees.add(mpropdef)
		mpropdef.callers.add(self)
		cuc += 1
	end

	fun compatible_site(site: MOPropSite): Bool is abstract
end

# Pattern of expression sites (method call / read attribute)
abstract class MOExprSitePattern
	super MOSitePattern

	redef type S: MOExprSite
end

# Pattern of method call
class MOCallSitePattern
	super MOExprSitePattern
	super MOPropSitePattern

	redef type GP: MMethod

	redef type LP: MMethodDef

	redef type S: MOCallSite

	#
	init(rst: MType, gp: MMethod)
	do
		self.rst = rst
		self.gp = gp

		var rsc = rst.get_mclass(sys.vm).as(not null)

		if not rsc.abstract_loaded then return

		for lp in gp.living_mpropdefs do
			if lp.mclassdef.mclass.ordering.has(rsc) then
				add_lp(lp)
			end
		end
	end

	redef fun compatible_site(site: MOPropSite)
	do
		return site isa MOCallSite
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

	# Compile the property
	fun compile_mo
	do
		for pattern in callers do
			pattern.cuc -= 1
		end
	end

	# Return expression of the propdef (null if procedure)
	var return_expr: nullable MOExpr is noinit, writable

	# An object is never return if return_expr is not a MOVar
	fun return_expr_is_object: Bool do return return_expr isa MOVar

	# List of instantiations sites in this local property
	var monews = new List[MONew]

	# List of object sites in this local property
	var mosites = new List[MOSite]
end

redef class MMethod
	redef type LP: MMethodDef

	redef type PATTERN: MOCallSitePattern

	redef fun add_propdef(mpropdef)
	do
		super

		var ordering = mpropdef.mclassdef.mclass.ordering

		for pattern in patterns do
			var rsc = pattern.rst.get_mclass(sys.vm).as(not null)

			if rsc.abstract_loaded and ordering.has(rsc) then
				pattern.add_lp(mpropdef)
			end
		end
	end
end

redef class MMethodDef
	redef type P: MOCallSitePattern
end

# Root hierarchy of MO entities
abstract class MOEntity
	fun pretty_print(file: FileWriter)
	do
	end
end

# Root hierarchy of expressions
abstract class MOExpr
	super MOEntity
end

# MO of variables
abstract class MOVar
	super MOExpr

	# The Variable objet refered by this node
	var variable: Variable

	# The offset of the variable in it environment, or the position of parameter
	var offset: Int

	# Compute concrete receivers (see MOCallSite / MOSite)
	fun compute_concretes(concretes: List[MClass]): Bool is abstract

	#
	fun valid_and_add_dep(dep: MOExpr, concretes: List[MClass]): Bool
	do
		if dep isa MONew then
			var cls = dep.pattern.cls
			if not concretes.has(cls) then concretes.add(cls)
			return true
		end
		return false
	end

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

	redef fun compute_concretes(concretes) do return valid_and_add_dep(dependency, concretes)

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
			if not valid_and_add_dep(dep, concretes) then return false
		end
		return true
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

	redef fun compute_concretes(concretes) do return false
end

# MO of instantiation sites
class MONew
	super MOExpr

	# The local property containing this site
	var lp: MPropDef

	# The pattern of this site
	var pattern: MONewPattern is writable, noinit

	# TODO: remove the cast to MMethodDef
	init(mpropdef: MPropDef)
	do
		lp = mpropdef
		lp.monews.add(self)
	end
end

# MO of super calls
class MOSuper
#	super MOCallSite
	super MOExpr

	# It's very complex to write a good code for ast2mo for ASuperExpr (it depends of a super call on init or regular method)
	# So, for now, MOSuper is an expression
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

	# The local property containing this expression
	var lp: MPropDef

	# The pattern using by this expression site
	var pattern: P is writable, noinit

	# List of concretes receivers if ALL receivers can be statically and with intra-procedural analysis determined
	var concretes_receivers: nullable List[MClass] is noinit, writable

	fun pattern_factory(rst: MType, gp: MProperty): P is abstract

	# Compute the concretes receivers.
	# If return null, drop the list (all receivers can't be statically and with intra-procedural analysis determined)
	private fun compute_concretes
	do
		if expr_recv isa MOVar then
			if not expr_recv.as(MOVar).compute_concretes(concretes_receivers.as(not null)) then
				concretes_receivers.as(not null).clear
			end
		end
	end

	# Get concretes receivers (or return empty list)
	fun get_concretes: List[MClass]
	do
		if concretes_receivers == null then
			concretes_receivers = new List[MClass]
			compute_concretes
		end
		return concretes_receivers.as(not null)
	end

	init(ast: AExpr, mpropdef: MPropDef)
	do
		self.ast = ast
		lp = mpropdef
		lp.mosites.add(self)
	end
end

# MO of a subtype test site
abstract class MOSubtypeSite
	super MOExprSite

	redef type P: MOSubtypeSitePattern

	# Static type on which the test is applied
	var target: MType

	init(ast: AExpr, mpropdef: MPropDef, target: MType)
	do
		super
		self.target = target
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

	redef fun pattern_factory(rst, gp)
	do
		return new MOCallSitePattern(rst, gp.as(MMethod))
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
end

# MO of read attribute
class MOReadSite
	super MOExprSite
	super MOAttrSite

	redef type P: MOReadSitePattern

	redef fun pattern_factory(rst, gp)
	do
		return new MOReadSitePattern(rst, gp.as(MAttribute))
	end

	# Tell if the attribute is immutable, useless at the moment
	var immutable = false
end

# MO of write attribute
class MOWriteSite
	super MOAttrSite

	redef type P: MOWriteSitePattern

	redef fun pattern_factory(rst, gp)
	do
		return new MOWriteSitePattern(rst, gp.as(MAttribute))
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
	var new_pattern = new MONewPattern(self)

	# List of patterns of subtypes test
	var subtype_pattern = new List[MOSubtypeSitePattern]

	# The only asnotnull pattern
	var asnotnull_pattern: nullable MOAsNotNullPattern

	# `self` is an instance of object
	fun is_instance_of_object(vm:VirtualMachine): Bool
	do
		return self.in_hierarchy(vm.mainmodule).greaters.length == 1
	end

	# Create (if not exists) and set a pattern for object subtype sites
	fun set_asnotnull_pattern(site: MOAsNotNullSite): MOAsNotNullPattern
	do
		if asnotnull_pattern == null then
			asnotnull_pattern = new MOAsNotNullPattern(mclass_type)
		end

		site.pattern = asnotnull_pattern.as(not null)
		return asnotnull_pattern.as(not null)
	end

	fun set_subtype_pattern(site: MOSubtypeSite)
	do
		var pattern: nullable MOSubtypeSitePattern = null

		for p in subtype_pattern do
			if p.rst == mclass_type and p.target == site.target then
				pattern = p
				break
			end
		end

		if pattern == null then
			pattern = new MOSubtypeSitePattern(mclass_type, site.target)
			subtype_pattern.add(pattern)
		end

		pattern.add_site(site)
	end

	# Create (if not exists) and set a pattern for objet prop sites
	fun set_site_pattern(site: MOPropSite, gp: MProperty)
	do
		var pattern: nullable MOPropSitePattern = null

		for p in sites_patterns do
			if p.gp == gp and p.rst == mclass_type and p.compatible_site(site) then
				pattern = p
				break
			end
		end

		if pattern == null then
			pattern = site.pattern_factory(mclass_type, gp)
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
end

redef class VirtualMachine
	# The top of list is the type of the receiver that will be used after new_frame
	var next_receivers = new List[MType]

	redef fun new_frame(node, mpropdef, args)
	do
		next_receivers.push(args.first.mtype)
		var ret = super(node, mpropdef, args)
		next_receivers.pop
		return ret
	end

end

redef class MType
	# True if self is a primitive type
	fun is_primitive_type: Bool
	do
		if self.to_s == "Int" then return true
		if self.to_s == "nullable Int" then return true
		if self.to_s == "String" then return true
		if self.to_s == "nullable String" then return true
		if self.to_s == "Char" then return true
		if self.to_s == "nullable Char" then return true
		if self.to_s == "Bool" then return true
		return false
	end

	# Get the class of the type
	fun get_mclass(vm: VirtualMachine): nullable MClass
	do
		if self isa MNullType then
			return null
		else if self isa MNotNullType then
			return self.mtype.get_mclass(vm)
		else if self isa MClassType then
			return self.mclass
		else if self isa MNullableType then
			return self.mtype.get_mclass(vm)
		else if (self isa MVirtualType or self isa MParameterType) and need_anchor then
			var anchor: MClassType
			var anchor_type = vm.next_receivers.last

			if anchor_type isa MNullableType then
				anchor = anchor_type.mtype.as(MClassType)
			else
				anchor = anchor_type.as(MClassType)
			end

			return anchor_to(vm.mainmodule, anchor).get_mclass(vm)
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
	# Return a MOEntity it's already created (already in the clone table).
	# Otherwise, create it, set it in clone table, set it's dependencies, return it.
	fun ast2mo(mpropdef: MPropDef): MOEntity is abstract

	# Generic ast2mo function for primitive nodes
	fun ast2mo_generic_primitive(mpropdef: MPropDef): MOEntity
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity

		sys.ast2mo_clone_table[self] = sys.moprimitive
		return sys.moprimitive
	end

	# Generic ast2mo function for literal nodes
	fun ast2mo_generic_literal(mpropdef: MPropDef): MOEntity
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity

		sys.ast2mo_clone_table[self] = sys.moliteral
		return sys.moliteral
	end

	# Return the MOEntity if it's already in the clone table
	fun get_mo_from_clone_table: nullable MOEntity
	do
		if sys.ast2mo_clone_table.has_key(self) then
			return sys.ast2mo_clone_table[self]
		end
		return null
	end

	fun copy_site(mpropdef: MPropDef): MOEntity is abstract
end

redef class AAttrFormExpr
	# Return the MOEntity if it's already in the clone table
	# redef fun get_mo_from_clone_table: nullable MOEntity
	# do
	# 	var mo_entity = super

	# 	if mo_entity != null then return mo_entity
	# 	if n_expr.mtype isa MNullType or n_expr.mtype == null then return sys.monull

	# 	return null
	# end

	redef fun get_receiver
	do
		return n_expr
	end

	redef fun ast2mo(mpropdef)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity

		var attr_site = copy_site(mpropdef).as(MOAttrSite)

		sys.ast2mo_clone_table[self] = attr_site
		var recv = get_receiver
		attr_site.expr_recv = recv.ast2mo(mpropdef).as(MOExpr)

		var recv_class = recv.mtype.as(not null).get_mclass(vm).as(not null)
		recv_class.set_site_pattern(attr_site, mproperty.as(not null))

		return attr_site
	end
end

redef class AAttrExpr
	redef fun copy_site(mpropdef: MPropDef): MOReadSite
	do
		return new MOReadSite(self, mpropdef)
	end
end

redef class AIssetAttrExpr
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

class ASubtypeExpr
	super AExpr

	redef fun ast2mo(mpropdef)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity

		var recv = get_receiver
		# if recv.mtype isa MNullType or recv.mtype == null then return sys.monull

		# TODO: be sure that cast_type is never null here
		var cast_site = copy_site(mpropdef).as(MOSubtypeSite)
		sys.ast2mo_clone_table[self] = cast_site
		cast_site.expr_recv = recv.ast2mo(mpropdef).as(MOExpr)

		var recv_class = recv.mtype.as(not null).get_mclass(vm).as(not null)
		recv_class.set_subtype_pattern(cast_site)

		return cast_site
	end
end

redef class AIsaExpr
	super ASubtypeExpr

	redef fun get_receiver
	do
		return n_expr
	end

	# Copy from AAttrFormExpr
	# redef fun get_mo_from_clone_table: nullable MOEntity
	# do
	# 	var mo_entity = super

	# 	if mo_entity != null then return mo_entity
	# 	# var recv = get_receiver
	# 	# if recv.mtype isa MNullType or recv.mtype == null then return sys.monull

	# 	return null
	# end

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
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity

		var moexpr = copy_site(mpropdef)
		sys.ast2mo_clone_table[self] = moexpr

		moexpr.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)

		var recv_class = n_expr.mtype.as(not null).get_mclass(vm).as(not null)
		recv_class.set_asnotnull_pattern(moexpr)

		return moexpr
	end
end

redef class Variable
	# Create the movar corresponding to AST node, and return it
	fun get_movar(mpropdef: MPropDef, node: ANode): MOVar
	do
		if sys.var2mo_clone_table.has_key(self) then return sys.var2mo_clone_table[self]

		if dep_exprs.length == 0 and parameter then
			var moparam = new MOParam(self, position)
			sys.var2mo_clone_table[self] = moparam
			return moparam
		else if dep_exprs.length == 1 or dep_exprs.length == 0 then
			var mossa = new MOSSAVar(self, position)
			sys.var2mo_clone_table[self] = mossa

			if dep_exprs.length == 0 then
				mossa.dependency = sys.monull
			else
				mossa.dependency = dep_exprs.first.ast2mo(mpropdef).as(MOExpr)
			end

			return mossa
		else
			assert dep_exprs.length > 1
			var mophi = new MOPhiVar(self, position)
			sys.var2mo_clone_table[self] = mophi

			for dep in dep_exprs do mophi.dependencies.add(dep.ast2mo(mpropdef).as(MOExpr))

			return mophi
		end
	end
end

redef class ANewExpr
	redef fun ast2mo(mpropdef)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity

		var monew = new MONew(mpropdef)
		sys.ast2mo_clone_table[self] = monew
		mpropdef.monews.add(monew)
		recvtype.as(not null).mclass.set_new_pattern(monew)
		return monew
	end
end

redef class ASelfExpr
	redef fun ast2mo(mpropdef)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity

		var movar = new MOParam(variable.as(not null), 0)
		sys.ast2mo_clone_table[self] = movar
		return movar
	end
end

redef class AVarExpr
	redef fun ast2mo(mpropdef)
	do
		return variable.as(not null).get_movar(mpropdef, self)
	end
end

redef class APropdef
	# Compute the implementation of sites of this local property when AST node is compiled
	redef fun compile(vm)
	do
		super

		if self isa AMethPropdef then

			for site in object_sites do
				site.ast2mo(mpropdef.as(not null))
			end

			mpropdef.return_expr = returnvar.get_movar(mpropdef.as(not null), self)

			mpropdef.compile_mo
		end
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

		var recv_class = n_expr.mtype.as(not null).get_mclass(vm).as(not null)
		recv_class.set_site_pattern(moattr, called_node_ast.mpropdef.as(not null).mproperty)

		return moattr
	end

	fun copy_site_method(mpropdef: MPropDef): MOCallSite
	do
		var cs = callsite.as(not null)
		var recv_class = cs.recv.get_mclass(vm).as(not null)
		var mocallsite = new MOCallSite(self, mpropdef)

		recv_class.set_site_pattern(mocallsite, cs.mproperty)

		return mocallsite
	end

	redef fun ast2mo(mpropdef)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity
		# if n_expr.mtype isa MNullType or n_expr.mtype == null then return sys.monull

		var cs = callsite.as(not null)

		# Static dispatch with global model to known if we handle method call of attribute access
		var called_node_ast = vm.modelbuilder.mpropdef2node(cs.mpropdef)
		var is_attribute = called_node_ast isa AAttrPropdef

		# ast2mo_accessor and ast2mo_method will add the node on the ast2mo_clone_table
		if is_attribute and not cs.mproperty.mpropdefs.length > 1 then
			return ast2mo_accessor(mpropdef, called_node_ast.as(AAttrPropdef))
		else
			return ast2mo_method(mpropdef, called_node_ast.as(not null), is_attribute)
		end
	end

	# Attribute access (with method call simulation: "foo.attr" instead on "foo._attr")
	fun ast2mo_accessor(mpropdef: MPropDef, called_node_ast: AAttrPropdef): MOEntity
	do
		var moattr = copy_site_accessor(mpropdef, called_node_ast)

		sys.ast2mo_clone_table[self] = moattr
		moattr.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)

		return moattr
	end

	# Real method call, and accessors with redefinitions
	# is_attribute is used only for stats (to kwon if it's a method call because of a redefinition of a attribute)
	fun ast2mo_method(mpropdef: MPropDef, called_node_ast: ANode, is_attribute: Bool): MOEntity
	do
		var mocallsite = copy_site_method(mpropdef)

		sys.ast2mo_clone_table[self] = mocallsite

		mocallsite.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)

		# Expressions arguments given to the method called
		for arg in raw_arguments do
			mocallsite.given_args.add(arg.ast2mo(mpropdef).as(MOExpr))
		end

		return mocallsite
	end
end

redef class AParExpr
	redef fun ast2mo(mpropdef)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity
		# if n_expr.mtype isa MNullType or n_expr.mtype == null then return sys.monull

		var moexpr = n_expr.ast2mo(mpropdef)
		sys.ast2mo_clone_table[self] = moexpr
		return moexpr
	end
end

redef class AOnceExpr
	redef fun ast2mo(mpropdef)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity
		# if n_expr.mtype isa MNullType or n_expr.mtype == null then return sys.monull

		var moexpr = n_expr.ast2mo(mpropdef)
		sys.ast2mo_clone_table[self] = moexpr
		return moexpr
	end
end

redef class ASuperExpr
	redef fun ast2mo(mpropdef)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity

		var mosuper = new MOSuper
		sys.ast2mo_clone_table[self] = mosuper
		return mosuper
	end

#	redef fun ast2mo(mpropdef) do
#		var mo_entity = get_mo_from_clone_table
#		if mo_entity != null then return mo_entity
#
#		var recv_class: MClass
#		var called_mproperty: MProperty
#
#		if callsite != null then
#			# super init call
#			var cs = callsite.as(not null)
#			recv_class = cs.recv.get_mclass(vm).as(not null)
#			called_mproperty = cs.mproperty
#		else
#			# super standard call
#			called_mproperty = self.mpropdef.as(not null).mproperty
#			recv_class = called_mproperty.intro_mclassdef.mclass
#		end
#
#		var mosuper = new MOSuperSite(self, mpropdef)
#		sys.ast2mo_clone_table[self] = mosuper
#
#		recv_class.set_site_pattern(mosuper, recv_class.mclass_type, called_mproperty)
#
#		mosuper.expr_recv = n_args.n_exprs.first.ast2mo(mpropdef).as(MOExpr)
#
#		# Expressions arguments given to the method called
#		for i_arg in [1..n_args.n_exprs.length] do
#			mosuper.given_args.add(n_args.n_exprs[i_arg].ast2mo(mpropdef).as(MOExpr))
#		end
#
#		return mosuper
#	end
end

redef class ANullExpr
	redef fun ast2mo(mpropdef) do return sys.monull
end

redef class AStringExpr
	redef fun ast2mo(mpropdef) do return ast2mo_generic_primitive(mpropdef)
end

redef class ASuperstringExpr
	redef fun ast2mo(mpropdef) do return ast2mo_generic_primitive(mpropdef)
end

redef class ACharExpr
	redef fun ast2mo(mpropdef) do return ast2mo_generic_primitive(mpropdef)
end

redef class AIntExpr
	redef fun ast2mo(mpropdef) do return ast2mo_generic_primitive(mpropdef)
end

redef class AFloatExpr
	redef fun ast2mo(mpropdef) do return ast2mo_generic_primitive(mpropdef)
end

redef class ABoolExpr
	redef fun ast2mo(mpropdef) do return ast2mo_generic_primitive(mpropdef)
end

redef class AArrayExpr
	redef fun ast2mo(mpropdef) do return ast2mo_generic_literal(mpropdef)
end
