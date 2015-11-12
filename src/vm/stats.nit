
# Statistics of the VM (implementations, preexistence...)
module stats

import vm_optimizations

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

	var dump_ast: FileWriter is noinit

	var dump_object_sites: FileWriter is noinit

	var all_ast_sites = new HashSet[AExpr]
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule, arguments)
	do
		sys.print_site_state = toolcontext.print_site_state.value
		sys.print_location_preexist = toolcontext.print_location_preexist.value

		super(mainmodule, arguments)

		if toolcontext.stats_on.value then
			pstats.overview

			post_exec(mainmodule)
			pstats.overview

			pstats.trace_patterns
			pstats.trace_sites
			pstats.trace_global_methods
			pstats.trace_local_methods
		end
	end

	# At the end of execution, check if counters are rights, recompile all methods to get upper bound
	# of preexistence (see redef in vm_optimizations)
	fun post_exec(mainmodule: MModule)
	do
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

		for method in sys.pstats.compiled_methods do
			if method isa MMethodDef then
				sys.pstats.get_method_return_origin(method)
			end
		end

		if sys.print_location_preexist then
			dump_location.as(not null).close
		end

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

		sys.pstats.loaded_classes_explicits += 1
	end

	redef fun load_class_indirect(mclass)
	do
		if mclass.abstract_loaded then return

		super(mclass)

		if mclass.kind == abstract_kind and not mclass.mclass_type.is_primitive_type then
			sys.pstats.loaded_classes_abstracts += 1
		else
			sys.pstats.loaded_classes_implicits += 1
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

		# Initialize the matrix of results
		var matrix_length = 80
		sys.pstats.matrix = new Array[Array[Int]].with_capacity(matrix_length)
		for i in [0..matrix_length[ do
			sys.pstats.matrix[i] = new Array[Int].filled_with(0, 6)
		end

		if sys.debug_mode then
			# Create the files for dumping ast_sites and model_sites
			sys.dump_ast = new FileWriter.open("dump_ast_sites.txt")
			sys.dump_object_sites = new FileWriter.open("dump_object_sites.txt")
		end
	end
end

redef class APropdef
	redef fun compile(vm)
	do
		super
		sys.pstats.nb_ast_sites += object_sites.length

		if sys.debug_mode then
			sys.all_ast_sites.add_all(object_sites)
		end
	end
end

redef class AAttrPropdef
	# When the node encode accessors who are redefined, tell if it's already count as "attr_redef"
	var attr_redef_taken_into = false
end

# Stats of the optimizing model
class MOStats
	# List of analysed sites
	var analysed_sites = new List[MOSite]

	# List of compiled methods
	var compiled_methods = new List[MPropDef]

	# List of new site compiled
	var compiled_new = new List[MONew]

	# The number of new sites in AST
	var new_sites: Int = 0

	# Number of mo_entities
	var object_sites: Int = 0

	# Label to display on dump
	var lbl: String

	# The number of executed AST sites
	var nb_ast_sites: Int = 0

	# The number of explicitly loaded classes
	var loaded_classes_explicits: Int = 0

	# The number of implicitly (i.e. indirectly) loaded classes
	var loaded_classes_implicits: Int = 0

	# The number of loaded abstract classes
	var loaded_classes_abstracts: Int = 0

	# The number of MOSite with a primitive receiver
	var nb_primitive_sites: Int = 0

	# The general matrix of the statistics
	var matrix: Array[Array[Int]] = new Array[Array[Int]]

	# Return an array which contains all captions of the statistics for the x axis
	fun caption_x: Array[String]
	do
		var res = new Array[String].with_capacity(7)

		res.add(",")
		res.add("method,")
		res.add("attribute,")
		res.add("cast,")
		res.add("asnotnull,")
		res.add("rst null,")
		res.add("total\n")

		return res
	end

	# Return an array which contains all captions of the statistics for the y axis
	fun caption_y: Array[String]
	do
		var res = new Array[String].with_capacity(75)

		res.add("self,")
		res.add("preexist,")
		res.add("npreexist,")
		res.add("concretes,")
		res.add("concretes preexist,")
		res.add("concretes npreexist,")
		res.add("static,")
		res.add("static preexist,")
		res.add("static npreexist,")
		res.add("sst,")
		res.add("sst preexist,")
		res.add("sst npreexist,")
		res.add("ph,")
		res.add("ph preexist,")
		res.add("ph npreexist,")
		res.add("null,")
		res.add("null preexist,")
		res.add("null npreexist,")
		res.add("\n,")
		res.add("optimisable inline,")
		res.add("non optimisable inline,")
		res.add("non inline,")
		res.add("\n,")
		res.add("from new,")
		res.add("from new preexist,")
		res.add("from new no preexist,")
		res.add("from return,")
		res.add("from return preexist,")
		res.add("from return non-preexisting,")
		res.add("from other preexisting,")
		res.add("from other non-preexisting,")
		res.add("from readsite,")
		res.add("\n,")
		res.add("callers positive cuc,")
		res.add("callers null cuc,")
		res.add("\n,")
		res.add("inter procedural return from new,")
		res.add("inter procedural return from other,")
		res.add("from primitive/lit,")
		res.add("procedure,")
		res.add("\n,")
		res.add("compiled new of unloaded classes,")
		res.add("ast sites,")
		res.add("new sites,")
		res.add("object sites,")
		res.add("mo_supers,")
		res.add("primitive_sites,")
		res.add("\n,")
		res.add("procedures,")
		res.add("methods with a return,")
		res.add("methods with a preexisting return,")
		res.add("methods with a non-preexisting return,")
		res.add("\n")
		res.add("preexisting patterns,")
		res.add("non-preexisting patterns with positive cuc,")
		res.add("non-preexisting pattern with null cuc,")
		res.add("no return pattern,")
		res.add("patterns without callees,")
		res.add("not executed patterns,")
		res.add("nb_patterns,")
		res.add("sites with preexisting return,")
		res.add("sites with non-preexisting return,")
		res.add("no return sites,")
		res.add("not executed sites,")
		res.add("\n")
		res.add("total self,")
		res.add("static self,")
		res.add("sst self,")
		res.add("ph self,")
		res.add("null self,")
		return res
	end

	fun trace_patterns
	do
		var file = new FileWriter.open("trace_patterns.txt")

		for pattern in sys.vm.all_patterns do
			file.write("{pattern.trace} {pattern}\n")
		end

		file.close
	end

	fun trace_sites
	do
		var file = new FileWriter.open("trace_sites.txt")

		print "sys.vm.all_moentities {sys.vm.all_moentities.length}"
		for mosite in sys.vm.all_moentities do
			if mosite isa MOSite then
				# Do not print the primitive sites
				if mosite.expr_recv.preexistence_origin.bin_and(16) != 16 then
					file.write("{mosite.trace} {mosite}\n")
				end
			end

			if sys.debug_mode then
				if mosite.ast != null then
					sys.dump_object_sites.write("{mosite} {mosite.ast.as(not null)}\n")
				else
					sys.debug_file.write("ERROR {mosite} without ast\n")
					sys.dump_object_sites.write("{mosite} null\n")
				end
			end
		end

		if sys.debug_mode then
			for ast_site in sys.all_ast_sites do
				if ast_site.mo_entity != null then
					sys.dump_ast.write("{ast_site.mo_entity.as(not null)} {ast_site}\n")
				else
					sys.dump_ast.write("{ast_site} null\n")
				end
			end

			sys.dump_object_sites.close
			sys.dump_ast.close
		end

		file.close
	end

	fun trace_local_methods
	do
		var file = new FileWriter.open("trace_local_methods.txt")

		for mpropdef in sys.vm.compiled_mproperties do
			file.write("{mpropdef.trace}\n")
		end

		file.close
	end

	fun trace_global_methods
	do
		var file = new FileWriter.open("trace_global_methods.txt")

		for mmethod in sys.vm.compiled_global_methods do
			file.write("{mmethod.trace}\n")
		end

		file.close
	end

	# Make text csv file contains overview statistics
	fun overview
	do
		if sys.disable_preexistence_extensions then
			lbl += "-original"
		else
			lbl += "-extend"
		end

		var file = new FileWriter.open("statistics-{lbl}.csv")

		# optimizable_inline: method_preexist_static + attribute_preexist_sst + cast_preexist_static + cast_preexist_sst + null_preexist (total)
		pstats.matrix[19][0] = pstats.matrix[7][0] + pstats.matrix[10][1] + pstats.matrix[7][2] + pstats.matrix[10][2] + pstats.matrix[16][5]

		# non optimizable inline: npreexist_static + attribute_npreexist_sst + cast_npreexist_sst + null_npreexist (total)
		pstats.matrix[20][0] = pstats.matrix[8][5] + pstats.matrix[11][1] + pstats.matrix[11][2] + pstats.matrix[17][5]

		# non_inline: total_ph + method_sst + asnotnull_sst
		pstats.matrix[21][0] = pstats.matrix[12][5] + pstats.matrix[9][0] + pstats.matrix[9][3]

		# cuc: caller uncompiled
		var cuc_pos = 0
		var cuc_null = 0

		var trace_file = new FileWriter.open("trace_file.txt")
		var trace_model = new FileWriter.open("trace_model.txt")

		# Statistics on method returns
		var nb_method_return = 0 # A method with a return
		var nb_procedure = 0 # Number of procedures
		var nb_method_return_pre = 0 # A method with a preexisting return
		var nb_method_return_npre = 0 # A method with a non-preexisting return

		for propdef in sys.vm.compiled_mproperties do
			if not propdef isa MMethodDef then continue
			if propdef.callers.length > 0 then
				if propdef.callers.first.cuc == 0 then
					cuc_null += 1
				else
					cuc_pos += 1
				end
			end

			# Debug the two model
			# debug_model(propdef, trace_file, trace_model)
			if propdef.msignature.return_mtype != null and propdef.return_expr != null then
				nb_method_return += 1

				var primitive_return = false
				if propdef.msignature.return_mtype.is_primitive_type then primitive_return = true

				# If the propdef has a preexisting return
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
			else
				nb_procedure += 1
			end
		end

		trace_file.close
		trace_model.close

		pstats.matrix[33][0] = cuc_pos
		pstats.matrix[34][0] = cuc_null

		# compiled "new" of unloaded classes at the end of execution
		var compiled_new_unloaded = 0
		for newsite in sys.vm.all_new_sites do
			if not newsite.pattern.cls.abstract_loaded then
				compiled_new_unloaded += 1
				print("UNLOADED {newsite} class = {newsite.pattern.cls}")
			end
		end

		pstats.matrix[41][0] = compiled_new_unloaded

		pstats.matrix[42][0] = sys.pstats.nb_ast_sites
		pstats.matrix[43][0] = sys.vm.all_new_sites.length
		pstats.matrix[44][0] = sys.vm.all_moentities.length
		pstats.matrix[45][0] = sys.vm.mo_supers.length
		pstats.matrix[46][0] = sys.pstats.nb_primitive_sites

		pstats.matrix[48][0] = nb_procedure
		pstats.matrix[49][0] = nb_method_return
		pstats.matrix[50][0] = nb_method_return_pre
		pstats.matrix[51][0] = nb_method_return_npre

		# Print the captions of the statistics file
		for caption in caption_x do
			file.write(caption)
		end

		# Go into each pattern to collect statistics on them
		for pattern in sys.vm.all_patterns do
			# If the pattern is a callsitepattern with a return
			if not pattern.is_executed then
				pstats.matrix[58][pattern.index_x] += 1
			end

			if pattern isa MOCallSitePattern then

				if pattern.callees.length == 0 then
					pstats.matrix[57][0] += 1

					# The pattern has no callees but was executed
					if pattern.is_executed == true then
						# Several possibilities: the receiver static class is not loaded or the global property is a particular method like != or ==
						print "Pattern {pattern.rsc}#{pattern.gp} executed but without callees {pattern.gp.living_mpropdefs}, rsc loaded ? = {pattern.rsc.abstract_loaded}"
					end
				else
					if pattern.gp.intro.msignature.return_mtype == null then
						pstats.matrix[56][0] += 1
					else
						# A preexisting pattern is a pattern with cuc = 0 and all callees with a preexisting return
						if pattern.is_pre and pattern.cuc == 0 then
							pstats.matrix[53][0] += 1
						else
							if pattern.cuc > 0 then
								pstats.matrix[54][0] += 1
							else
								pstats.matrix[55][0] += 1
							end
						end
					end
				end
			end

			# All patterns are counted here
			pstats.matrix[59][pattern.index_x] += 1
			pstats.matrix[59][5] += 1
		end

		for i in [0..pstats.matrix.length[ do
			# Write the caption on the line if any
			if i < caption_y.length then file.write(caption_y[i])

			# Then print the statistics
			var size = pstats.matrix[i].length
			for j in [0..size[ do
				var value = pstats.matrix[i][j]
				if value != 0 then file.write(value.to_s)

				file.write(",")
			end
			file.write("\n")
		end

		file.close
	end

	fun debug_model(propdef: MPropDef, trace_file: FileWriter, trace_model: FileWriter)
	do
		# Trace of AST model
		trace_file.write("full_name {propdef.full_name} location {propdef.location} ")

		if propdef.return_expr != null then
			trace_file.write("preexistence {propdef.return_expr.return_preexist}\n")
		end

		# Get the corresponding APropdef
		var node = sys.vm.modelbuilder.mpropdef2node(propdef)
		if node isa APropdef then
			trace_file.write("Return dependences {node.returnvar.dep_exprs}\n")

			# trace of MO model
			trace_model.write("full_name {propdef.full_name} location {propdef.location} ")

			if propdef.return_expr != null then
				trace_model.write("return_expr.preexistence {propdef.return_expr.return_preexist}\n")
			end

			trace_model.write("Return dependences {node.returnvar.dep_exprs}\n")

			for site in propdef.mosites do
				trace_model.write("\t")

				if site isa MOCallSite then
					if site.trace_origin == 32 and site.expr_recv.preexistence_origin == 3 then
						print "concretes_receivers"
					end
				end

				trace_model.write("\n")
			end
			trace_model.write("\n")

			# Verify that the variables of the two models are equal
			var i = 0
			if propdef.variables.length != node.variables.length then
				print "Problem in {propdef} {node.location}"
				print "MOVAR.Length = {propdef.variables.length} VARIABLE.length {node.variables.length.to_s}"
			else
				for variable in node.variables do
					trace_model.write("{variable.name} dep_exprs.length {variable.dep_exprs.length}" + "\n\t")
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
		loaded_classes_explicits = counters.loaded_classes_explicits
		loaded_classes_implicits = counters.loaded_classes_implicits
		loaded_classes_abstracts = counters.loaded_classes_abstracts
		analysed_sites.add_all(counters.analysed_sites)
		compiled_methods.add_all(counters.compiled_methods)
		compiled_new.add_all(counters.compiled_new)
		nb_ast_sites = counters.nb_ast_sites

		new_sites = sys.vm.all_new_sites.length
		object_sites = sys.vm.all_moentities.length

		matrix = new Array[Array[Int]].with_capacity(counters.matrix.length)
		for i in [0..counters.matrix.length[ do
			matrix[i] = counters.matrix[i]
		end
	end

	# Tell where the return of method is come from
	fun get_method_return_origin(method: MMethodDef)
	do
		if method.return_expr_is_object then
			# If the method return an object, it's return_expr is a MOVar
			method.return_expr.as(MOVar).return_stats(method.mproperty)
		else if method.return_expr != null then
			pstats.matrix[37][0] += 1
		else
			pstats.matrix[38][0] += 1
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
	# All MOSite have an index in x to be identified in results,
	# The index represents the type of the site: method, attribute, cast or asnotnull
	var index_x: Int = 0

	# The type of the site (used for debug),
	# can be a method, attribute, cast or asnotnull
	var site_type: String is noinit

	# Origin of the dependence encoded with the method `preexistence_origin`
	var origin: Int is noinit

	# Count the implementation of the site
	fun stats(vm: VirtualMachine)
	do
		expr_recv.expr_preexist
		origin = expr_recv.preexistence_origin

		# If the receiver is not a primitive
		if not origin.bin_and(16) == 16 then
			incr_from_site
			incr_concrete_site
			incr_self
			incr_rst_unloaded(vm)

			if print_site_state then
				var buf = "site {self}\n"
				buf += "\tpattern: {pattern2str}\n"
				buf += "\tlp: {lp.mclassdef.name}::{lp.name}\n"
				buf += "\tlocation: {ast.location}\n"
				# TODO: fix the mutability of preexistence
				buf += "\tpreexist/mutable: {expr_recv.is_pre}/{expr_recv.expr_preexist.bit_npre_immut}\n"
				buf += "\timpl: {get_impl(vm)}\n"
				print(buf)
			end

			var origin = expr_recv.preexistence_origin
			sys.vm.receiver_origin[origin] += 1
			sys.vm.receiver_origin[sys.vm.receiver_origin.length -1] += 1

			# Trace the origin of preexistence of callsites
			if self isa MOCallSite then
				sys.vm.trace_origin[trace_origin] += 1
				sys.vm.trace_origin[sys.vm.trace_origin.length-1] += 1
			end

			pstats.matrix[get_impl(vm).compute_index_y(self)][index_x] += 1

			# Increment the total for implementation of the previous line
			incr_total

			# Increment statistics on callsites
			incr_stats_sites
		else
			# Increment the total of sites with a primitive receiver
			sys.pstats.nb_primitive_sites += 1
		end
	end

	# Print the pattern (RST/GP or target class for subtype test)
	fun pattern2str: String is abstract

	fun incr_stats_sites
	do
		if not is_executed then
			pstats.matrix[63][index_x] += 1
		end

		# If self isa MOCallsite and call a method with a return
		if self isa MOCallSite then
			if pattern.as(MOCallSitePattern).gp.intro.msignature.return_mtype != null then
				# If the pattern is preexisting, then the site is also preexisting
				if pattern.as(MOCallSitePattern).cuc == 0 and pattern.as(MOCallSitePattern).is_pre then
					pstats.matrix[60][0] += 1
				else
					# If the site is preexisting with concretes receivers for example, the site is preexisting
					if compute_preexist.bit_pre then
						pstats.matrix[60][0] += 1
					else
						# For all other cases, the site is non-preexisting
						pstats.matrix[61][0] += 1
					end
				end
			else
				if pattern.as(MOCallSitePattern).gp.intro.msignature.return_mtype == null then
					pstats.matrix[62][0] += 1
				end
			end
		end
	end

	fun incr_total
	do
		var impl = get_impl(vm)
		var pre = expr_recv.is_pre

		pstats.matrix[impl.index_y][index_x] += 1
		pstats.matrix[impl.index_y][5] += 1
		pstats.matrix[impl.compute_index_y(self)][5] += 1

		# The total of preexisting sites
		if pre then
			pstats.matrix[1][index_x] += 1
			pstats.matrix[1][5] += 1
		else
			pstats.matrix[2][index_x] += 1
			pstats.matrix[2][5] += 1
		end
	end

	# Trace origins of preexistence
	fun incr_from_site
	do
		# If the receiver comes only from a new
		if origin == 2 or origin == 130 then
			pstats.matrix[23][index_x] += 1
			pstats.matrix[23][5] += 1

			if expr_recv.is_pre then
				pstats.matrix[24][index_x] += 1
				pstats.matrix[24][5] += 1
			else
				pstats.matrix[25][index_x] += 1
				pstats.matrix[25][5] += 1
			end
		end

		# If the receiver comes only from a callsite
		if origin == 4 or origin == 132 then
			# The total of callsites
			pstats.matrix[26][index_x] += 1
			pstats.matrix[26][5] += 1

			# If the receiver is preexisting
			if origin.bin_and(128) == 0 then
				if not sys.disable_preexistence_extensions then
					pstats.matrix[27][index_x] += 1
					pstats.matrix[27][5] += 1
				end
			else
				pstats.matrix[28][index_x] += 1
				pstats.matrix[28][5] += 1
			end
		end

		# If the receiver comes only from an attribute read
		if origin == 256 or origin == 384 then
			pstats.matrix[31][index_x] += 1
			pstats.matrix[31][5] += 1
		end

		# Other cases, a combination of several origins in extended preexistence (parameters and literals are excluded)
		if not origin == 2 and not origin == 130 and not origin == 4 and not origin == 132 and not origin == 256 and not origin == 384 then
			# We also filter the receiver which come from a parameter or a literal
			if not origin == 1 and not origin == 8 then
				# If the site is preexisting
				if origin.bin_and(128) == 0 then
					pstats.matrix[29][index_x] += 1
					pstats.matrix[29][5] += 1
				else
					pstats.matrix[30][index_x] += 1
					pstats.matrix[30][5] += 1
				end
			end
		end
	end

	# Increment counters for callsites with concrete receivers
	fun incr_concrete_site
	do
		if get_concretes != null then
			# Total of concretes for each category
			pstats.matrix[3][index_x] += 1

			# Total of concretes
			pstats.matrix[3][5] += 1

			# Preexisting and non-preexisting sites with concretes
			if expr_recv.is_pre then
				pstats.matrix[4][index_x] += 1
				pstats.matrix[4][5] += 1
			else
				pstats.matrix[5][index_x] += 1
				pstats.matrix[5][5] += 1
			end
		end
	end

	# Increment counters if the receiver is `self`
	fun incr_self
	do
		if expr_recv isa MOParam and expr_recv.as(MOParam).offset == 0 then
			pstats.matrix[0][index_x] += 1
			pstats.matrix[0][5] += 1
		end

		# Recopy the total of self sites
		if expr_recv isa MOParam and expr_recv.as(MOParam).offset == 0 then
			pstats.matrix[65][index_x] += 1
			pstats.matrix[65][5] += 1

			# Increment for each implementation with self as a receiver
			var impl = get_impl(sys.vm)
			if impl isa StaticImpl then
				pstats.matrix[66][index_x] += 1
				pstats.matrix[66][5] += 1
			else if impl isa SSTImpl then
				pstats.matrix[67][index_x] += 1
				pstats.matrix[67][5] += 1
			else if impl isa PHImpl then
				pstats.matrix[68][index_x] += 1
				pstats.matrix[68][5] += 1
			else if impl isa NullImpl then
				pstats.matrix[69][index_x] += 1
				pstats.matrix[69][5] += 1
			end
		end
	end

	# Increment counters if the receiver static class is unloaded
	fun incr_rst_unloaded(vm: VirtualMachine)
	do
		var rst_loaded = pattern.rsc.abstract_loaded

		if not rst_loaded then
			var impl = get_impl(vm)

			pstats.matrix[impl.index_y][4] += 1
			pstats.matrix[impl.compute_index_y(self)][4] += 1

			# Increment the total of preexisting and non-preexisting
			if expr_recv.is_pre then
				pstats.matrix[1][4] += 1
			else
				pstats.matrix[2][4] += 1
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

	fun trace: String
	do
		var res = "recv {expr_recv} "
		if concretes_receivers != null then
			res += "concretes = {concretes_receivers.as(not null)}"
		else
			res += "concretes = null"
		end

		res += " impl {get_impl(sys.vm)} preexistence {expr_recv.compute_preexist} preexistence_origin {expr_recv.preexistence_origin}"

		return res
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

redef class MOPropSite
	redef fun pattern2str do return "{pattern.rst}::{pattern.gp}"

	redef fun trace
	do
		return super + " {pattern.rsc}#{pattern.gp} is_executed = {is_executed}"
	end
end

redef class MOCallSite
	redef var index_x = 0

	redef var site_type = "method"

	redef fun trace
	do
		var res = " {pattern.rsc}#{pattern.gp} args {given_args}"

		return super + res
	end
end

redef class MOAttrSite
	redef var index_x = 1

	redef var site_type = "attribute"
end

redef class MOSubtypeSite
	redef fun pattern2str do return "{pattern.rst}->{pattern.target}"

	redef var index_x = 2

	redef var site_type = "cast"
end

redef class MOAsNotNullSite
	redef fun pattern2str do return "{pattern.rst}->not null"

	redef var site_type = "asnotnull"

	redef var index_x = 3
end

redef class MOSitePattern
	var index_x: Int = 5
end

redef class MOCallSitePattern
	redef var index_x = 0
end

redef class MOAttrPattern
	redef var index_x = 1
end

redef class MOSubtypeSitePattern
	redef var index_x = 2
end

redef class MOAsNotNullPattern
	redef var index_x = 3
end

redef class Implementation
	# All Implementation are associated with an index in y
	var index_y: Int = 6

	# Compute the y index of this implementation
	# `mosite` The site which contains the implementation
	fun compute_index_y(mosite: MOSite): Int
	do
		if mosite.expr_recv.is_pre then
			return index_y + 1
		else
			return index_y + 2
		end
	end
end

redef class StaticImpl
	redef var index_y = 6
end

redef class SSTImpl
	redef var index_y = 9
end

redef class PHImpl
	redef var index_y = 12
end

redef class NullImpl
	redef var index_y = 15
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

redef class MMethod

	fun trace: String
	do
		return "{intro_mclassdef.mclass}#{name} nb patterns {patterns.length}"
	end
end

redef class MPropDef
	redef fun compile_mo
	do
		super

		for site in self.mosites do
			site.stats(vm)
			sys.pstats.analysed_sites.add(site)
		end

		for newexpr in self.monews do
			sys.pstats.new_sites += 1
		end

		sys.pstats.compiled_methods.add(self)

		if self isa MMethodDef then
			sys.pstats.get_method_return_origin(self)
		end
	end

	fun trace: String
	do
		var res = "MProperty {mproperty}, self {self}, mosites {mosites.length}, monews {monews.length}, callers {callers.length}"

		if return_expr != null then
			res += " {return_expr.return_preexist}"
		end

		return res
	end
end

redef class MOVar
	# Get the origin of return variable (tell if it comes from a new expression), with inter-procedural analysis
	fun return_stats(mproperty: MProperty)
	do
		var callees = new List[MProperty]
		callees.add(mproperty)
		if trace_origin(self, callees) then
			pstats.matrix[36][0] += 1
		else
			pstats.matrix[37][0] += 1
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

redef class ASendExpr
	redef fun ast2mo_method(mpropdef, called_node_ast, is_attribute)
	do
		var sup = super

		# It's an accessors (with redefs) dispatch
		if is_attribute and not called_node_ast.as(AAttrPropdef).attr_redef_taken_into then
			called_node_ast.as(AAttrPropdef).attr_redef_taken_into = true
		end

		return sup
	end

	redef fun expr(v)
	do
		if mo_entity != null then
			mo_entity.as(MOSite).set_executed
		end

		return super
	end
end

redef class ASendReassignFormExpr
	redef fun stmt(v)
	do
		if mo_entity != null then
			mo_entity.as(MOSite).set_executed
		end

		super
	end
end
redef class AAttrExpr
	redef fun expr(v)
	do
		if mo_entity != null then
			mo_entity.as(MOSite).set_executed
		end

		var res = super
		return res
	end
end

redef class AAttrAssignExpr
	redef fun stmt(v)
	do
		if mo_entity != null then
			mo_entity.as(MOSite).set_executed
		end
		super
	end
end

redef class AAttrReassignExpr
	redef fun stmt(v)
	do
		if mo_entity != null then
			mo_entity.as(MOSite).set_executed
		end
		super
	end
end

redef class AIsaExpr
	redef fun expr(v)
	do
		if mo_entity != null then
			mo_entity.as(MOSite).set_executed
		end

		var res = super
		return res
	end
end

redef class AAsCastForm
	redef fun expr(v)
	do
		if mo_entity != null then
			mo_entity.as(MOSite).set_executed
		end

		var res = super
		return res
	end
end
