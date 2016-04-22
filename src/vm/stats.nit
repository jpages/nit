# Statistics of the VM (implementations, preexistence...)
module stats

import vm_optimizations

# Avoid to write same thing everytimes
private fun incr_specific_counters(cond: Bool, yes: String, no: String)
do
	if cond then
		pstats.inc(yes)
	else
		pstats.inc(no)
	end
end

# Avoid to write the same thing...
private fun incr_rst(rst_loaded: Bool, lbl: String)
do
	if not rst_loaded then pstats.inc("rst_unloaded_" + lbl)
end

redef class ToolContext
	# Enable print stats
	var stats_on = new OptionBool("Display statistics of model optimizing / preexistence after execution", "--mo-stats")

	# Enable print site state
	var print_site_state = new OptionBool("Display state of a MOSite (preexistence, impl)", "--site-state")

	# Enable print location of preexists sites
	var print_location_preexist = new OptionBool("Dump the location of preexist site", "--location-preexist")

	redef init
	do
		super
		option_context.add_option(stats_on)
		option_context.add_option(print_site_state)
		option_context.add_option(print_location_preexist)
	end
end

redef class Sys
	# Preexist counters
	var pstats = new MOStats("first") is writable

	# Access to print_site_state from anywhere
	var print_site_state: Bool = false

	# Access to location-preexist information from anywhere
	var print_location_preexist: Bool = false

	# Used to put location of preexist sites
	var dump_location: nullable FileWriter = null
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule, arguments)
	do
		sys.print_site_state = toolcontext.print_site_state.value
		sys.print_location_preexist = toolcontext.print_location_preexist.value

		super(mainmodule, arguments)

		if toolcontext.stats_on.value then
			print(pstats.pretty)
			pstats.overview

			post_exec(mainmodule)
			pstats.overview

			pstats.trace_patterns
			# Meh...
		end
	end

	# At the end of execution, check if counters are rights, recompile all methods to get upper bound
	# of preexistence (see redef in vm_optimizations)
	fun post_exec(mainmodule: MModule)
	do
		# Recompile all active objet sites to get the upper bound of the preexistence
		# We don't need pstats counters with lower bound anymore, so we override it

		sys.vm.init_stats

		var old_counters = sys.pstats
		sys.pstats = new MOStats("last")
		sys.pstats.copy_data(old_counters)

		if sys.print_location_preexist then
			dump_location = new FileWriter.open("mo-stats-location")
		end

		for expr in sys.vm.all_moexprs do expr.preexist_init

		for site in pstats.analysed_sites
		do
			site.lp.preexist_analysed = false

			site.site_preexist

			site.impl = null
			site.get_impl(sys.vm)
			site.stats(sys.vm)
		end

		for method in sys.pstats.compiled_methods do sys.pstats.get_method_return_origin(method)

		if sys.print_location_preexist then
			dump_location.as(not null).close
		end

		print(pstats.pretty)

		# Print the array of preexistence values
		print("Stats on receiver_origin\n")
		var receiver_origin_string = """# Allows to trace the preexistence origin of a Site by encoding the following values:
		# 1: parameter
		# 2: a new
		# 4: a call
		# 8: a lit
		# 16: a primitive
		# 32: null receiver
		# 64: recursive
		# 128: is_npre
		# 256: a readsite"""
		print(receiver_origin_string)
		for i in [0..sys.vm.receiver_origin.length[ do
			if sys.vm.receiver_origin[i] > 0 then print("receiver_origin[{i}] = {sys.vm.receiver_origin[i]}")
		end

		print("\nStats on return_origin\n")
		for i in [0..sys.vm.return_origin.length[ do
			if sys.vm.return_origin[i] > 0 then print("return_origin[{i}] = {sys.vm.return_origin[i]}")
		end

		# print("Stats on receiver_origin_recursive\n")
		# for i in [0..sys.vm.receiver_origin_recursive.length[ do
		# 	if sys.vm.receiver_origin_recursive[i] > 0 then print("receiver_origin_recursive[{i}] = {sys.vm.receiver_origin_recursive[i]}")
		# end

		# print("\nStats on return_origin_recursive\n")
		# for i in [0..sys.vm.return_origin_recursive.length[ do
		# 	if sys.vm.return_origin_recursive[i] > 0 then print("return_origin_recursive[{i}] = {sys.vm.return_origin_recursive[i]}")
		# end

		var trace_origin_string = """
		# Trace the origin of preexistence of a site
		# 1: positive cuc
		# 2: at least one preexisting callee
		# 4: at least one non-preexisting callee
		# 8: the callee is a procedure
		# 16: the expression is preexisting
		# 32: concretes types
		# 64: generic/formal receiver
		"""
		print(trace_origin_string)

		for i in [0..sys.vm.trace_origin.length[ do
			if sys.vm.trace_origin[i] > 0 then print("trace_origin[{i}] = {sys.vm.trace_origin[i]}")
		end
	end
end

redef class VirtualMachine
	redef fun load_class(mclass)
	do
		if mclass.loaded then return

		super(mclass)

		pstats.inc("loaded_classes_explicits")
	end

	redef fun load_class_indirect(mclass)
	do
		if mclass.abstract_loaded then return

		super(mclass)

		if mclass.kind == abstract_kind and not mclass.mclass_type.is_primitive_type then
			pstats.inc("loaded_classes_abstracts")
		else
			pstats.inc("loaded_classes_implicits")
		end
	end

	var return_origin: Array[Int] is noinit

	var receiver_origin: Array[Int] is noinit

	var return_origin_recursive: Array[Int] is noinit

	var receiver_origin_recursive: Array[Int] is noinit

	var trace_origin: Array[Int] is noinit

	init
	do
		init_stats
	end

	fun init_stats
	do
		return_origin = new Array[Int].filled_with(0, 129)
		receiver_origin = new Array[Int].filled_with(0, 513)
		return_origin_recursive = new Array[Int].filled_with(0, 129)
		receiver_origin_recursive = new Array[Int].filled_with(0, 257)
		trace_origin = new Array[Int].filled_with(0, 257)
	end
end

redef class APropdef
	#
	redef fun compile(vm)
	do
		super
		sys.pstats.map["ast_sites"] = sys.pstats.map["ast_sites"] + object_sites.length
	end
end

redef class AAttrPropdef
	# When the node encode accessors who are redefined, tell if it's already count as "attr_redef"
	var attr_redef_taken_into = false
end

redef class ASendExpr
	redef fun ast2mo_method(mpropdef, called_node_ast, is_attribute)
	do
		var sup = super

		# It's an accessors (with redefs) dispatch
		if is_attribute and not called_node_ast.as(AAttrPropdef).attr_redef_taken_into then
			pstats.inc("attr_redef")
			called_node_ast.as(AAttrPropdef).attr_redef_taken_into = true
		end

		return sup
	end
end

# Stats of the optimizing model
class MOStats
	# List of analysed sites
	var analysed_sites = new List[MOSite]

	# List of compiled methods
	var compiled_methods = new List[MMethodDef]

	# List of new site compiled
	var compiled_new = new List[MONew]

	# Label to display on dump
	var lbl: String

	# Internal encoding of counters
	var map = new HashMap[String, Int]

	# Increment a counter
	fun inc(el: String) do map[el] += 1

	# Decrement a counter
	fun dec(el: String)
	do
		map[el] -= 1
		assert map[el] >= 0
	end

	# Get a value
	fun get(el: String): Int do return map[el]

	# Dump and format all values
	fun dump(prefix: String): String
	do
		var ret = ""

		for key, val in map do ret += "{prefix}{key}: {val}\n"

		return ret
	end

	fun trace_patterns
	do
		var file = new FileWriter.open("trace_patterns.txt")

		for pattern in sys.vm.all_patterns do
			file.write("{pattern.trace} {pattern}\n")
		end

		file.close
	end

	# Make text csv file contains overview statistics
	fun overview
	do
		var buf: String
		var file = new FileWriter.open("mo-stats-{lbl}.csv")

		file.write(", method, attribute, cast, total, rst null\n")

		var self_meth = map["method_self"]
		var self_attr = map["attribute_self"]
		var self_cast = map["cast_self"]
		var self_sum = self_meth + self_attr + self_cast

		file.write("self, {self_meth}, {self_attr}, {self_cast}, {self_sum}, \n")

		file.write("preexist, {map["method_preexist"]}, {map["attribute_preexist"]}, {map["cast_preexist"]}, {map["preexist"]}, \n")
		file.write("preexist_primitive, {map["method_preexist_primitive"]}, {map["attribute_preexist_primitive"]}, {map["cast_preexist_primitive"]}, {map["preexist_primitive"]}\n")
		file.write("npreexist, {map["method_npreexist"]}, {map["attribute_npreexist"]}, {map["cast_npreexist"]}, {map["npreexist"]}, \n")

		buf = "{map["method_concretes"]},"
		buf += "{map["attribute_concretes"]},"
		buf += "{map["cast_concretes"]},"
		buf += "{map["concretes"]}"
		file.write("concretes,{buf},\n")

		buf = "{map["method_concretes_preexist"]},"
		buf += "{map["attribute_concretes_preexist"]},"
		buf += "{map["cast_concretes_preexist"]},"
		buf += "{map["concretes_preexist"]}"
		file.write("concretes preexist,{buf},\n")

		buf = "{map["method_concretes_npreexist"]},"
		buf += "{map["attribute_concretes_npreexist"]},"
		buf += "{map["cast_concretes_npreexist"]},"
		buf += "{map["concretes_npreexist"]}"
		file.write("concretes npreexist,{buf},\n")

		file.write("static, {map["method_static"]}, {map["attribute_static"]}, {map["cast_static"]}, {map["static"]}, {map["rst_unloaded_static"]}\n")

		buf = "{map["method_preexist_static"]},"
		buf += "{map["attribute_preexist_static"]},"
		buf += "{map["cast_preexist_static"]},"
		buf += "{map["static_preexist"]},"
		buf += "{map["rst_unloaded_static_pre"]}"
		file.write("static preexist, {buf}\n")

		buf = "{map["method_npreexist_static"]},"
		buf += "{map["attribute_npreexist_static"]},"
		buf += "{map["cast_npreexist_static"]},"
		buf += "{map["static_npreexist"]},"
		buf += "{map["rst_unloaded_static_npre"]}"
		file.write("static npreexist, {buf}\n")

		file.write("sst, {map["method_sst"]}, {map["attribute_sst"]}, {map["cast_sst"]}, {map["sst"]}, {map["rst_unloaded_sst"]}\n")

		buf = "{map["method_preexist_sst"]},"
		buf += "{map["attribute_preexist_sst"]},"
		buf += "{map["cast_preexist_sst"]},"
		buf += "{map["sst_preexist"]},"
		buf += "{map["rst_unloaded_sst_pre"]}"
		file.write("sst preexist, {buf}\n")

		buf = "{map["method_npreexist_sst"]},"
		buf += "{map["attribute_npreexist_sst"]},"
		buf += "{map["cast_npreexist_sst"]},"
		buf += "{map["sst_npreexist"]},"
		buf += "{map["rst_unloaded_sst_npre"]}"
		file.write("sst npreexist, {buf}\n")

		file.write("ph, {map["method_ph"]}, {map["attribute_ph"]}, {map["cast_ph"]}, {map["ph"]}, {map["rst_unloaded_ph"]}\n")

		buf = "{map["method_preexist_ph"]},"
		buf += "{map["attribute_preexist_ph"]},"
		buf += "{map["cast_preexist_ph"]},"
		buf += "{map["ph_preexist"]},"
		buf += "{map["rst_unloaded_ph_pre"]}"
		file.write("ph preexist, {buf}\n")

		buf = "{map["method_npreexist_ph"]},"
		buf += "{map["attribute_npreexist_ph"]},"
		buf += "{map["cast_npreexist_ph"]},"
		buf += "{map["ph_npreexist"]},"
		buf += "{map["rst_unloaded_ph_npre"]}"
		file.write("ph npreexist, {buf}\n")

		file.write("null, {map["method_null"]}, {map["attribute_null"]}, {map["cast_null"]}, {map["null"]}, {map["rst_unloaded_null"]}\n")

		buf = "{map["method_preexist_null"]},"
		buf += "{map["attribute_preexist_null"]},"
		buf += "{map["cast_preexist_null"]},"
		buf += "{map["null_preexist"]},"
		buf += "{map["rst_unloaded_null_pre"]}"
		file.write("null preexist, {buf}\n")

		buf = "{map["method_npreexist_null"]},"
		buf += "{map["attribute_npreexist_null"]},"
		buf += "{map["cast_npreexist_null"]},"
		buf += "{map["null_npreexist"]},"
		buf += "{map["rst_unloaded_null_npre"]}"
		file.write("null npreexist, {buf}\n")

		file.write("\n\n")

		var optimizable_inline = map["method_preexist_static"] + map["attribute_preexist_sst"] + map["cast_preexist_static"] + map["cast_preexist_sst"]
		file.write("optimisable inline,{optimizable_inline}\n")

		var no_optimizable = map["method_npreexist_static"] + map["attribute_npreexist_sst"] + map["cast_npreexist_sst"] + map["cast_npreexist_static"]
		file.write("non optimisable inline,{no_optimizable}\n")

		var no_inline = map["method_ph"] + map["method_sst"] + map["attribute_ph"] + map["cast_ph"]
		file.write("non inline,{no_inline}\n")

		file.write("\n\n")

		# from new

		file.write("from new,{map["method_sites_from_new"]}, {map["attribute_sites_from_new"]},{map["cast_sites_from_new"]},{map["sites_from_new"]}\n")

		buf = "{map["method_sites_from_new_pre"]},"
		buf += "{map["attribute_sites_from_new_pre"]},"
		buf += "{map["cast_sites_from_new_pre"]},"
		buf += "{map["sites_from_new_pre"]}"
		file.write("from new preexist,{buf}\n")

		buf = "{map["method_sites_from_new_npre"]},"
		buf += "{map["attribute_sites_from_new_npre"]},"
		buf += "{map["cast_sites_from_new_npre"]},"
		buf += "{map["sites_from_new_npre"]}"
		file.write("from new no preexist,{buf}\n")

		# from method return

		buf = "{map["method_sites_from_meth_return"]},"
		buf += "{map["attribute_sites_from_meth_return"]},"
		buf += "{map["cast_sites_from_meth_return"]},"
		buf += "{map["sites_from_meth_return"]}"
		file.write("from return,{buf}\n")

		buf = "{map["method_sites_from_meth_return_cuc_null"]},"
		buf += "{map["attribute_sites_from_meth_return_cuc_null"]},"
		buf += "{map["cast_sites_from_meth_return_cuc_null"]},"
		buf += "{map["sites_from_meth_return_cuc_null"]}"
		file.write("from return cuc null,{buf}\n")

		buf = "{map["method_sites_from_meth_return_cuc_null_pre"]},"
		buf += "{map["attribute_sites_from_meth_return_cuc_null_pre"]},"
		buf += "{map["cast_sites_from_meth_return_cuc_null_pre"]},"
		buf += "{map["sites_from_meth_return_cuc_null_pre"]}"
		file.write("from return cuc null preexist,{buf}\n")

		buf = "{map["method_sites_from_meth_return_cuc_null_npre"]},"
		buf += "{map["attribute_sites_from_meth_return_cuc_null_npre"]},"
		buf += "{map["cast_sites_from_meth_return_cuc_null_npre"]},"
		buf += "{map["sites_from_meth_return_cuc_null_npre"]}"
		file.write("from return cuc null no preexist,{buf}\n")

		buf = "{map["method_sites_from_meth_return_cuc_pos"]},"
		buf += "{map["attribute_sites_from_meth_return_cuc_pos"]},"
		buf += "{map["cast_sites_from_meth_return_cuc_pos"]},"
		buf += "{map["sites_from_meth_return_cuc_pos"]}"
		file.write("from return cuc pos,{buf}\n")

		# from read site

		buf = "{map["method_sites_from_read"]},"
		buf += "{map["attribute_sites_from_read"]},"
		buf += "{map["cast_sites_from_read"]},"
		buf += "{map["sites_from_read"]}"
		file.write("from readsite,{buf}\n")

		# cuc

		file.write("\n")

		var living_propdefs = new HashSet[MMethodDef]
		for site in analysed_sites do
			if site isa MOCallSite then
				for lp in site.pattern.gp.living_mpropdefs do
					# The hashset make duplicates if the site is already in (!!!??!!)
					if not living_propdefs.has(site.lp) then
						living_propdefs.add(lp)
					end
				end
			end
		end

		var cuc_pos = 0
		var cuc_null = 0

		var trace_file = new FileWriter.open("trace_file.txt")
		var trace_model = new FileWriter.open("trace_model.txt")

		# Statistics on method returns
		var nb_method_return = 0 # A method with a return
		var nb_method_return_pre = 0 # A method with a preexisting return
		var nb_method_return_npre = 0 # A method with a non-preexisting return

		for propdef in sys.vm.compiled_mproperties do
			assert propdef isa MMethodDef
			if propdef.callers.length > 0 then
				if propdef.callers.first.cuc == 0 then
					cuc_null += 1
				else
					cuc_pos += 1
				end
			end

			# Debug the two model
			debug_model(propdef, trace_file, trace_model)
			if propdef.msignature.return_mtype != null and propdef.return_expr != null then
				nb_method_return += 1

				var primitive_return = false
				if propdef.msignature.return_mtype.is_primitive_type then primitive_return = true

				# If the propdef has a preexisting returns
				if propdef.return_expr.is_pre and not primitive_return then
					nb_method_return_pre += 1
					# Trace the origin of preexistence
					var origin = propdef.return_expr.preexistence_origin

					sys.vm.return_origin[origin] += 1
					sys.vm.return_origin[sys.vm.return_origin.length-1] += 1

					# var recursive = propdef.return_expr.preexistence_origin_recursive
					# sys.vm.return_origin_recursive[recursive] += 1
					# sys.vm.return_origin_recursive[sys.vm.return_origin_recursive.length-1] += 1
				else
					nb_method_return_npre += 1
				end
			end
		end

		trace_file.close
		trace_model.close

		file.write("callers cuc pos, {cuc_pos}\n")
		file.write("callers cuc null, {cuc_null}\n")

		# return from new with inter-procedural analysis
		file.write("\n")
		file.write("inter procedural return from new, {map["inter_return_from_new"]}\n")
		file.write("inter procedural return from other, {map["inter_return_from_other"]}\n")
		file.write("from primitive/lit, {map["return_from_not_object"]}\n")
		file.write("procedure, {map["procedure"]}\n")

		# compiled "new" of unloaded class at the end of execution
		file.write("\n")
		var compiled_new_unloaded = 0
		for newsite in sys.vm.all_new_sites do
			if not newsite.pattern.cls.abstract_loaded then
				compiled_new_unloaded += 1
				print("UNLOADED {newsite} class = {newsite.pattern.cls}")
			end
		end

		file.write("compiled new of unloaded classes, {compiled_new_unloaded}")

		file.write("\n")
		file.write("ast sites, {map["ast_sites"]}\n")
		file.write("new sites, {sys.vm.all_new_sites.length}\n")
		file.write("object sites, {map["object_sites"]}\n")

		file.write("\n")
		file.write("methods with a return, {nb_method_return}\n")
		file.write("methods with a preexisting return, {nb_method_return_pre}\n")
		file.write("methods with a non-preexisting return, {nb_method_return_npre}\n")

		file.close
	end

	# Pretty format
	fun pretty: String
	do
		var ret = ""

		ret += "\n------------------ MO STATS {lbl} ------------------\n"
		ret += dump("\t")
		ret += "--------------------------------------------------------\n"

		return ret
	end

	fun debug_model(propdef: MPropDef, trace_file: FileWriter, trace_model: FileWriter)
	do
		# Trace of Julien's model
		trace_file.write("full_name {propdef.full_name} location {propdef.location} ")

		if propdef.return_expr != null then
			trace_file.write("preexistence {propdef.return_expr.return_preexist}\n")
		end

		# Get the corresponding APropdef
		var node = sys.vm.modelbuilder.mpropdef2node(propdef)
		if node isa APropdef then
			trace_file.write("Return dependences {node.returnvar.dep_exprs}\n")

			for v in node.variables do
				trace_file.write("\t")

				v.pretty_print(trace_file)
				trace_file.write("\n")
			end
			trace_file.write("\n")

			# trace of Colin's model
			trace_model.write("full_name {propdef.full_name} location {propdef.location} ")

			if propdef.return_expr != null then
				trace_model.write("preexistence {propdef.return_expr.return_preexist}\n")
			end

			trace_model.write("Return dependences {node.returnvar.dep_exprs}\n")

			for site in propdef.mosites do
				trace_model.write("\t")

				site.pretty_print(trace_model)

				if site isa MOCallSite then
					if site.trace_origin == 32 and site.expr_recv.preexistence_origin == 3 then
						print "concretes_receivers"
					end
				end

				trace_model.write("\n")
			end
			trace_model.write("\n")


			# Verify variables of the two models
			var i = 0
			if propdef.variables.length != node.variables.length then
				print "Problem in {propdef} {node.location}"
				print "MOVAR.Length = {propdef.variables.length} VARIABLE.length {node.variables.length.to_s}"
			else
				for variable in node.variables do
					trace_model.write("MOVAR"+i.to_s+"\n\t")
					propdef.variables[i].pretty_print_expr(trace_model)
					trace_model.write("\n")

					trace_model.write("Variable"+i.to_s+"\n\t")
					variable.pretty_print(trace_model)
					trace_model.write("\n")
					i += 1
				end
			end
		end
	end

	# Copy counters who not depends of the world state
	fun copy_data(counters: MOStats)
	do
		map["loaded_classes_explicits"] = counters.get("loaded_classes_explicits")
		map["loaded_classes_implicits"] = counters.get("loaded_classes_implicits")
		map["loaded_classes_abstracts"] = counters.get("loaded_classes_abstracts")
		map["attr_redef"] = counters.get("attr_redef")
		map["sites_final"] = counters.get("sites_final")
		analysed_sites.add_all(counters.analysed_sites)
		compiled_methods.add_all(counters.compiled_methods)
		compiled_new.add_all(counters.compiled_new)
		map["ast_sites"] = counters.get("ast_sites")
		map["new_sites"] = sys.vm.all_new_sites.length
	end

	init
	do
		# inrc when a class is explicitly (with a "new" keyword) loaded
		map["loaded_classes_explicits"] = 0

		# inrc when a class is loaded as super-class (abstract excluded) of a loaded class (implicit or explicit)
		map["loaded_classes_implicits"] = 0

		# incr when a class is abstract and loaded as super-class
		map["loaded_classes_abstracts"] = 0

		# incr when the site depends at least of one return expression
		map["sites_from_meth_return"] = 0
		map["sites_from_meth_return_cuc_pos"] = 0
		map["sites_from_meth_return_cuc_null"] = 0
		map["sites_from_meth_return_cuc_null_pre"] = 0
		map["sites_from_meth_return_cuc_null_npre"] = 0

		map["method_sites_from_meth_return"] = 0
		map["method_sites_from_meth_return_cuc_pos"] = 0
		map["method_sites_from_meth_return_cuc_null"] = 0
		map["method_sites_from_meth_return_cuc_null_pre"] = 0
		map["method_sites_from_meth_return_cuc_null_npre"] = 0

		map["attribute_sites_from_meth_return"] = 0
		map["attribute_sites_from_meth_return_cuc_pos"] = 0
		map["attribute_sites_from_meth_return_cuc_null"] = 0
		map["attribute_sites_from_meth_return_cuc_null_pre"] = 0
		map["attribute_sites_from_meth_return_cuc_null_npre"] = 0

		map["cast_sites_from_meth_return"] = 0
		map["cast_sites_from_meth_return_cuc_pos"] = 0
		map["cast_sites_from_meth_return_cuc_null"] = 0
		map["cast_sites_from_meth_return_cuc_null_pre"] = 0
		map["cast_sites_from_meth_return_cuc_null_npre"] = 0

		# incr when the site depends at least of one new expression
		map["sites_from_new"] = 0
		map["method_sites_from_new"] = 0
		map["attribute_sites_from_new"] = 0
		map["cast_sites_from_new"] = 0

		map["sites_from_new_pre"] = 0
		map["method_sites_from_new_pre"] = 0
		map["attribute_sites_from_new_pre"] = 0
		map["cast_sites_from_new_pre"] = 0

		map["sites_from_new_npre"] = 0
		map["method_sites_from_new_npre"] = 0
		map["attribute_sites_from_new_npre"] = 0
		map["cast_sites_from_new_npre"] = 0

		# incr when the site depends at least of one attr read expression
		map["sites_from_read"] = 0
		map["method_sites_from_read"] = 0
		map["attribute_sites_from_read"] = 0
		map["cast_sites_from_read"] = 0

		# incr when the site depends of at least of one return expression or one new expression
		map["sites_handle_by_extend_preexist"] = 0

		# incr when the site is on leaf gp on global model
		map["sites_final"] = 0

		# incr if a site is preexist
		map["preexist"] = 0

		# incr if a site is a primitive (and so, preexists)
		map["preexist_primitive"] = 0

		# incr if a site isn't preexist
		map["npreexist"] = 0

		map["static"] = 0
		map["static_preexist"] = 0
		map["static_npreexist"] = 0
		map["sst"] = 0
		map["sst_preexist"] = 0
		map["sst_npreexist"] = 0
		map["ph"] = 0
		map["ph_preexist"] = 0
		map["ph_npreexist"] = 0
		map["null"] = 0
		map["null_preexist"] = 0
		map["null_npreexist"] = 0

		# incr if construct MO node to access on attribute as MOCallSite
		# because it's an accessors with redefinitions
		# If it's incr, some meth_* counters will be incr too, as regular method call
		map["attr_redef"] = 0

		map["concretes"] = 0
		map["concretes_preexist"] = 0
		map["concretes_npreexist"] = 0

		# access to self receiver
		map["self"] = 0

		map["rst_unloaded_static"] = 0
		map["rst_unloaded_static_pre"] = 0
		map["rst_unloaded_static_npre"] = 0
		map["rst_unloaded_sst"] = 0
		map["rst_unloaded_sst_pre"] = 0
		map["rst_unloaded_sst_npre"] = 0
		map["rst_unloaded_ph"] = 0
		map["rst_unloaded_ph_pre"] = 0
		map["rst_unloaded_ph_npre"] = 0
		map["rst_unloaded_null"] = 0
		map["rst_unloaded_null_pre"] = 0
		map["rst_unloaded_null_npre"] = 0

		map["method"] = 0
		map["method_preexist"] = 0
		map["method_preexist_primitive"] = 0
		map["method_npreexist"] = 0
		map["method_self"] = 0
		map["method_concretes"] = 0
		map["method_concretes_preexist"] = 0
		map["method_concretes_npreexist"] = 0
		map["method_static"] = 0
		map["method_preexist_static"] = 0
		map["method_npreexist_static"] = 0
		map["method_sst"] = 0
		map["method_preexist_sst"] = 0
		map["method_npreexist_sst"] = 0
		map["method_ph"] = 0
		map["method_preexist_ph"] = 0
		map["method_npreexist_ph"] = 0
		map["method_null"] = 0
		map["method_preexist_null"] = 0
		map["method_npreexist_null"] = 0

		map["attribute"] = 0
		map["attribute_preexist"] = 0
		map["attribute_preexist_primitive"] = 0
		map["attribute_npreexist"] = 0
		map["attribute_self"] = 0
		map["attribute_concretes"] = 0
		map["attribute_concretes_preexist"] = 0
		map["attribute_concretes_npreexist"] = 0
		map["attribute_static"] = 0
		map["attribute_preexist_static"] = 0
		map["attribute_npreexist_static"] = 0
		map["attribute_sst"] = 0
		map["attribute_preexist_sst"] = 0
		map["attribute_npreexist_sst"] = 0
		map["attribute_ph"] = 0
		map["attribute_preexist_ph"] = 0
		map["attribute_npreexist_ph"] = 0
		map["attribute_null"] = 0
		map["attribute_preexist_null"] = 0
		map["attribute_npreexist_null"] = 0

		map["cast"] = 0
		map["cast_preexist"] = 0
		map["cast_preexist_primitive"] = 0
		map["cast_npreexist"] = 0
		map["cast_self"] = 0
		map["cast_concretes"] = 0
		map["cast_concretes_preexist"] = 0
		map["cast_concretes_npreexist"] = 0
		map["cast_static"] = 0
		map["cast_preexist_static"] = 0
		map["cast_npreexist_static"] = 0
		map["cast_sst"] = 0
		map["cast_preexist_sst"] = 0
		map["cast_npreexist_sst"] = 0
		map["cast_ph"] = 0
		map["cast_preexist_ph"] = 0
		map["cast_npreexist_ph"] = 0
		map["cast_null"] = 0
		map["cast_preexist_null"] = 0
		map["cast_npreexist_null"] = 0

		map["asnotnull"] = 0
		map["asnotnull_preexist"] = 0
		map["asnotnull_preexist_primitive"] = 0
		map["asnotnull_npreexist"] = 0

		map["call_with_cuc_pos"] = 0
		map["call_with_cuc_null"] = 0

		map["inter_return_from_new"] = 0
		map["inter_return_from_other"] = 0
		map["return_from_not_object"] = 0
		map["procedure"] = 0

		map["ast_sites"] = 0
		map["new_sites"] = 0
		map["object_sites"] = 0
	end

	# Tell where the return of method is come from
	fun get_method_return_origin(method: MMethodDef)
	do
		if method.return_expr_is_object then
			# If the method return an object, it's return_expr is a MOVar
			method.return_expr.as(MOVar).return_stats(method.mproperty)
		else if method.return_expr != null then
			sys.pstats.inc("return_from_not_object")
		else
			sys.pstats.inc("procedure")
		end
	end
end

redef class MOExpr
	fun pretty_print_expr(file: FileWriter)
	do
		file.write("{self} Preexistence expr {expr_preexist} is pre = {is_pre}\n")
	end
end

redef class MOSSAVar
	redef fun pretty_print_expr(file)
	do
		super
		file.write(" {self.variable.name} with dep ")
		dependency.pretty_print(file)
	end
end

redef class MOPhiVar
	redef fun pretty_print_expr(file)
	do
		super
		file.write(" {self.variable.name} with deps ")
		for dep in dependencies do
			dep.pretty_print_expr(file)
		end
	end
end

redef class MOSite
	# Type of the site (method, attribute or cast)
	var site_type: String is noinit

	# Non-recursive origin of the dependency
	var origin: DependencyTrace is noinit

	# Count the implementation of the site
	fun stats(vm: VirtualMachine)
	do
		origin = new DependencyTrace(expr_recv)
		origin.trace
		incr_preexist(vm)

		if not origin.from_primitive then
			incr_from_site
			incr_concrete_site(vm)
			incr_self
			incr_rst_unloaded(vm)
			incr_type_impl(vm)

			if print_site_state then
				var buf = "site {self}\n"
				buf += "\tpattern: {pattern2str}\n"
				buf += "\tlp: {lp.mclassdef.name}::{lp.name}\n"
				buf += "\tlocation: {ast.location}\n"
				# TODO: fix that
				buf += "\tpreexist/mutable: {expr_recv.is_pre}/{expr_recv.expr_preexist.bit_npre_immut}\n"
				buf += "\timpl: {get_impl(vm)}\n"
				print(buf)
			end

			sys.pstats.inc("object_sites")

			var origin = expr_recv.preexistence_origin
			sys.vm.receiver_origin[origin] += 1
			sys.vm.receiver_origin[sys.vm.receiver_origin.length -1] += 1

			# var recursive = expr_recv.preexistence_origin_recursive
			# sys.vm.receiver_origin_recursive[recursive] += 1
			# sys.vm.receiver_origin_recursive[sys.vm.receiver_origin_recursive.length-1] += 1

			# Trace the origin of preexistence of callsites
			if self isa MOCallSite then
				if expr_recv.is_pre then
					print("{self} trace_origin {trace_origin} receiver_preexistence {expr_recv.expr_preexist} receiver_origin {expr_recv.preexistence_origin} nb_callees {nb_callees}")
				else
					print("{self} trace_origin {trace_origin} receiver_preexistence {expr_recv.expr_preexist} non-preexisting_receiver nb_callees {nb_callees}")
				end
				sys.vm.trace_origin[trace_origin] += 1
				sys.vm.trace_origin[sys.vm.trace_origin.length-1] += 1
			end
		end

		if print_location_preexist then dump_location_site
	end

	# Print the pattern (RST/GP or target class for subtype test)
	fun pattern2str: String is abstract

	# Print location of a site
	fun dump_location_site
	do
		# dump_location is null of first compilation, and set for last compilation
		if dump_location != null then
			var from2str = ""
			if expr_recv.is_pre then
				if origin.from_new then from2str += " from-new "
				if origin.from_param then from2str += " from-param "
				if origin.from_return then from2str += " from-return "
				if origin.from_primitive then from2str += " from-primitive "
				if origin.from_literal then from2str += " from-literal "
				if origin.from_super then from2str += " from-super "
			else
				from2str += "non-preexist"
			end

			dump_location.as(not null).write("{site_type} {ast.location} {from2str}\n")
		end
	end

	#
	fun incr_preexist(vm: VirtualMachine)
	do
		var pre = expr_recv.is_pre

		if pre and origin.from_primitive then
			sys.pstats.inc("preexist_primitive")
			sys.pstats.inc("{site_type}_preexist_primitive")
		else if pre then
			sys.pstats.inc("preexist")
			sys.pstats.inc("{site_type}_preexist")
		else
			sys.pstats.inc("npreexist")
			sys.pstats.inc("{site_type}_npreexist")
		end
	end

	#
	fun incr_type_impl(vm: VirtualMachine)
	do
		var impl = get_impl(vm)
		var pre = expr_recv.is_pre

		pstats.inc(site_type)

		if impl isa StaticImpl then
			pstats.inc("{site_type}_static")
			pstats.inc("static")
			incr_specific_counters(pre, "static_preexist", "static_npreexist")
			incr_specific_counters(pre, "{site_type}_preexist_static", "{site_type}_npreexist_static")
		else if impl isa SSTImpl then
			pstats.inc("{site_type}_sst")
			pstats.inc("sst")
			incr_specific_counters(pre, "sst_preexist", "sst_npreexist")
			incr_specific_counters(pre, "{site_type}_preexist_sst", "{site_type}_npreexist_sst")
		else if impl isa PHImpl then
			pstats.inc("{site_type}_ph")
			pstats.inc("ph")
			incr_specific_counters(pre, "ph_preexist", "ph_npreexist")
			incr_specific_counters(pre, "{site_type}_preexist_ph", "{site_type}_npreexist_ph")
		else if impl isa NullImpl then
			pstats.inc("{site_type}_null")
			pstats.inc("null")
			incr_specific_counters(pre, "null_preexist", "null_npreexist")
			incr_specific_counters(pre, "{site_type}_preexist_null", "{site_type}_npreexist_null")
		else
			abort
		end
	end

	# WARN : this partition is not exclusive
	fun incr_from_site
	do
		if origin.from_new then
			pstats.inc("sites_from_new")
			pstats.inc("{site_type}_sites_from_new")

			incr_specific_counters(expr_recv.is_pre, "sites_from_new_pre", "sites_from_new_npre")
			incr_specific_counters(expr_recv.is_pre, "{site_type}_sites_from_new_pre", "{site_type}_sites_from_new_npre")
		end

		if origin.from_return then
			pstats.inc("sites_from_meth_return")
			pstats.inc("{site_type}_sites_from_meth_return")

			incr_specific_counters(origin.cuc_null,
			"{site_type}_sites_from_meth_return_cuc_null",
			"{site_type}_sites_from_meth_return_cuc_pos")

			incr_specific_counters(origin.cuc_null, "sites_from_meth_return_cuc_null", "sites_from_meth_return_cuc_pos")

			if origin.cuc_null then
				incr_specific_counters(expr_recv.is_pre,
				"{site_type}_sites_from_meth_return_cuc_null_pre",
				"{site_type}_sites_from_meth_return_cuc_null_npre")

				incr_specific_counters(expr_recv.is_pre,
				"sites_from_meth_return_cuc_null_pre",
				"sites_from_meth_return_cuc_null_npre")
			end
		end

		if origin.from_read then
			pstats.inc("sites_from_read")
			pstats.inc("{site_type}_sites_from_read")
		end
	end

	#
	fun incr_concrete_site(vm: VirtualMachine)
	do
		if get_concretes != null then
			var pre = expr_recv.is_pre

			pstats.inc("concretes")
			pstats.inc("{site_type}_concretes")
			incr_specific_counters(pre, "concretes_preexist", "concretes_npreexist")
			incr_specific_counters(pre, "{site_type}_concretes_preexist", "{site_type}_concretes_npreexist")
		end
	end

	#
	fun incr_self
	do
		if expr_recv isa MOParam and expr_recv.as(MOParam).offset == 0 then
			pstats.inc("self")
			pstats.inc("{site_type}_self")
		end
	end

	#
	fun incr_rst_unloaded(vm: VirtualMachine)
	do
		var rst_loaded = pattern.rsc.abstract_loaded

		if not rst_loaded then
			var impl = get_impl(vm)
			var pre = expr_recv.is_pre

			if impl isa StaticImpl then
				pstats.inc("rst_unloaded_static")
				incr_specific_counters(pre, "rst_unloaded_static_pre", "rst_unloaded_static_npre")
			else if impl isa SSTImpl then
				pstats.inc("rst_unloaded_sst")
				incr_specific_counters(pre, "rst_unloaded_sst_pre", "rst_unloaded_sst_npre")
			else if impl isa PHImpl then
				pstats.inc("rst_unloaded_ph")
				incr_specific_counters(pre, "rst_unloaded_ph_pre", "rst_unloaded_ph_npre")
			else if impl isa NullImpl then
				pstats.inc("rst_unloaded_null")
				incr_specific_counters(pre, "rst_unloaded_null_pre", "rst_unloaded_null_npre")
			else
				abort
			end
		end
	end

	redef fun pretty_print(file)
	do
		file.write(self.to_s)
		file.write(" receiver \{\{")
		expr_recv.pretty_print_expr(file)
		file.write("\}\}")
	end
end

redef class MOExprSite
	redef fun pretty_print(file)
	do
		super
		file.write(" return [[")
		pretty_print_expr(file)
		file.write("]]")
	end
end

redef class MOCallSite
	redef var site_type = "method"
end

redef class AExpr
	fun pretty_print(file: FileWriter)
	do
		var d = new ASTDump
		d.enter_visit(self)
		d.write_to(file)
	end
end

redef class Variable
	fun pretty_print(file: FileWriter)
	do
		file.write(name)

		for dep in dep_exprs do
			file.write(" ")
			if dep isa AVarFormExpr then
				file.write(dep.variable.name)
			else
				dep.pretty_print(file)
			end
		end
	end
end

redef class AVarFormExpr
	redef fun pretty_print(file)
	do
		variable.pretty_print(file)
	end
end

redef class MOPropSite
	redef fun pattern2str do return "{pattern.rst}::{pattern.gp}"
end

redef class MOAttrSite
	redef var site_type = "attribute"
end

redef class MOSubtypeSite
	redef fun pattern2str do return "{pattern.rst}->{pattern.target}"

	redef var site_type = "cast"
end

redef class MOAsNotNullSite
	redef fun pattern2str do return "{pattern.rst}->not null"

	redef var site_type = "asnotnull"

	redef fun incr_type_impl(vm: VirtualMachine)
	do
	end

	redef fun incr_from_site do	end

	redef fun incr_concrete_site(vm: VirtualMachine)
	do
	end

	redef fun incr_self
	do
	end

	redef fun incr_rst_unloaded(vm: VirtualMachine)
	do
	end
end

redef class MPropDef
	redef fun compile_mo
	do
		super

		if self isa MMethodDef then
			for site in self.mosites do
				site.stats(vm)
				sys.pstats.analysed_sites.add(site)
			end

			for newexpr in self.monews do sys.pstats.inc("new_sites")
			sys.pstats.compiled_methods.add(self)
			sys.pstats.get_method_return_origin(self)
		end
	end
end

redef class MOVar
	# Get the origin of return variable (tell if it comes from a new expression), with inter-procedural analysis
	fun return_stats(mproperty: MProperty)
	do
		var callees = new List[MProperty]
		callees.add(mproperty)
		if trace_origin(self, callees) then
			sys.pstats.inc("inter_return_from_new")
		else
			sys.pstats.inc("inter_return_from_other")
		end
	end

	# Recurse while one of the dependency is not a new or callsite.
	# True if its come from only new expressions
	fun trace_origin(expr: MOExpr, callees: List[MProperty]): Bool
	do
		if expr isa MONew then
			return true
		else if expr isa MOCallSite and not callees.has(expr.pattern.gp) then
			# Recurse on all living local properties
			callees.add(expr.pattern.gp)
			for mpropdef in expr.pattern.gp.living_mpropdefs do
				if mpropdef.return_expr == null then return false
				if not trace_origin(mpropdef.return_expr.as(not null), callees) then return false
			end
			return true
		else if expr isa MOSSAVar then
			return trace_origin(expr.dependency, callees)
		else if expr isa MOPhiVar then
			for dep in expr.dependencies do
				if not trace_origin(dep, callees) then return false
			end
			return true
		else
			return false
		end
	end
end

# Tell where the expression of a site comes from
class DependencyTrace
	# from a new expression
	var from_new = false

	# from a return method expression
	var from_return = false

	# from a read attribute expression
	var from_read = false

	# from a parameter
	var from_param = false

	# from a literal
	var from_literal = false

	# from a primitive
	var from_primitive = false

	# from super
	var from_super = false

	# cuc is null ? usefull only when it comes from a method
	var cuc_null = true

	# the expression to trace
	var expr: MOExpr

	# trace the dependencies (entry point)
	fun trace do trace_internal(expr)

	# trace the dependencies (internal function)
	fun trace_internal(expr: MOExpr)
	do
		if expr isa MONew then
			from_new = true
		else if expr isa MOCallSite then
			from_return = true
			if expr.pattern.cuc > 0 then cuc_null = false
		else if expr isa MOReadSite then
			from_read = true
		else if expr isa MOParam then
			from_param = true
		else if expr isa MOLit then
			from_literal = true
		else if expr isa MOPrimitive or expr isa MOIsaSubtypeSite then
			from_primitive = true
		else if expr isa MOSuper then
			from_super = true
		else if expr isa MOSSAVar then
			trace_internal(expr.dependency)
		else if expr isa MOPhiVar then
			for dep in expr.dependencies do trace_internal(dep)
		end
	end
end
