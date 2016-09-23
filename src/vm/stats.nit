# This file is part of NIT ( http://www.nitlanguage.org ).
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

# Statistics of the VM (implementations, preexistence...)
module stats

import vm_optimizations
import dynamic_loading_ffi
import date

redef class ToolContext
	# Enable statistics on the model
	var stats_on = new OptionBool("Display statistics of model optimizing / preexistence after execution", "--mo-stats")

	redef init
	do
		super
		option_context.add_option(stats_on)
	end
end

redef class Sys
	var dump_ast: FileWriter is noinit

	var dump_object_sites: FileWriter is noinit

	var all_ast_sites = new HashSet[AExpr]
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule, arguments)
	do
		super(mainmodule, arguments)

		if toolcontext.stats_on.value then
			vm.pstats.statistics_model
			vm.pstats.trace_patterns
			vm.pstats.overview

			post_exec(mainmodule)
			vm.pstats.overview

			vm.pstats.trace_sites
			vm.pstats.trace_global_methods
			vm.pstats.trace_local_methods
		end
	end

	# At the end of execution, check if counters are rights, recompile all methods to get upper bound
	# of preexistence (see redef in vm_optimizations)
	fun post_exec(mainmodule: MModule)
	do
		sys.vm.init_stats

		var old_counters = sys.vm.pstats
		sys.vm.pstats = new MOStats("last")
		sys.vm.pstats.copy_data(old_counters)

		for expr in sys.vm.all_moexprs do expr.preexist_init

		for pic_pattern in sys.vm.all_picpatterns do pic_pattern.impl = null
		for pattern in sys.vm.all_patterns do pattern.impl = null

		vm.pstats.statistics_model
		vm.pstats.trace_patterns

		for site in vm.pstats.analysed_sites
		do
			site.lp.preexist_analysed = false

			site.expr_recv.preexist_init
			site.site_preexist

			site.impl = null
			site.get_impl(sys.vm)
			site.stats(sys.vm)
		end

		for monomorph_site in vm.pstats.analysed_monomorph_sites do
			monomorph_site.stats(vm)
		end

		for method in sys.vm.pstats.compiled_methods do
			if method isa MMethodDef then
				sys.vm.pstats.get_method_return_origin(method)
			end
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
		# 256: a readsite
		# 512: a cast"""
		print(receiver_origin_string)
		for i in [0..sys.vm.receiver_origin.length[ do
			if sys.vm.receiver_origin[i] > 0 then print("receiver_origin[{i}] = {sys.vm.receiver_origin[i]}")
		end

		print("\nStats on return_origin\n")
		for i in [0..sys.vm.return_origin.length[ do
			if sys.vm.return_origin[i] > 0 then print("return_origin[{i}] = {sys.vm.return_origin[i]}")
		end

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

		# trace the used classes
		var trace_classes = new FileWriter.open("{vm.pstats.dir}/trace_classes.txt")

		for mclass in vm.pstats.loaded_classes do
			trace_classes.write("{mclass} number of methods {mclass.mmethods.length} number of attributes {mclass.mattributes.length} ")
			trace_classes.write("nb_instances {mclass.nb_instances} direct_superclasses {mclass.in_hierarchy(sys.vm.mainmodule).direct_greaters.length}\n")
		end

		print "classes in suffixes {vm.suffixes}"
		print "nb classes in suffixes {vm.suffixes.length} methods {vm.suffixes_methods.length} attributes {vm.suffixes_attributes.length}"

		print "nb loaded_classes {vm.pstats.loaded_classes.length}"
		trace_classes.close
	end
end

redef class VirtualMachine
	redef fun load_class(mclass)
	do
		if mclass.loaded then return

		super(mclass)

		# Add the number of superclasses of this class (including self)
		var superclasses = mclass.in_hierarchy(mainmodule).greaters
		pstats.loaded_superclasses += superclasses.length

		for cl in superclasses do
			# If this class introduces some attributes
			if not cl.intro_mattributes.is_empty then
				pstats.loaded_superclasses_attributes += 1
			end
		end

		pstats.loaded_classes_explicits += 1

		pstats.loaded_classes.add(mclass)
	end

	redef fun load_class_indirect(mclass)
	do
		if mclass.abstract_loaded then return

		super(mclass)

		if mclass.kind == abstract_kind and not mclass.mclass_type.is_primitive_type then
			pstats.loaded_classes_abstracts += 1
		else
			pstats.loaded_classes_implicits += 1
		end
	end

	redef fun new_frame(node, mpropdef, args)
	do
		mpropdef.nb_executions += 1

		return super
	end

	redef fun init_instance(recv: Instance)
	do
		super

		recv.mtype.as(MClassType).mclass.nb_instances += 1
	end

	# The class to gather all statistics
	var pstats = new MOStats("first") is writable

	var return_origin: Array[Int] is noinit

	var receiver_origin: Array[Int] is noinit

	var return_origin_recursive: Array[Int] is noinit

	var receiver_origin_recursive: Array[Int] is noinit

	var trace_origin: Array[Int] is noinit

	# The set of classes which are in the attributes suffix of a class
	var suffixes_attributes = new HashSet[MClass]

	# The set of classes which are in the attributes suffix of a class
	var suffixes_methods = new HashSet[MClass]

	# All classes which are in a suffix (methods or attributes) of a class
	var suffixes = new HashSet[MClass]

	init
	do
		init_stats
	end

	fun init_stats
	do
		return_origin = new Array[Int].filled_with(0, 513)
		receiver_origin = new Array[Int].filled_with(0, 1025)
		return_origin_recursive = new Array[Int].filled_with(0, 257)
		receiver_origin_recursive = new Array[Int].filled_with(0, 257)
		trace_origin = new Array[Int].filled_with(0, 257)

		# Initialize the matrix of results
		var matrix_length = 90
		pstats.matrix = new Array[Array[Int]].with_capacity(matrix_length)
		for i in [0..matrix_length[ do
			pstats.matrix[i] = new Array[Int].filled_with(0, 6)
		end

		if sys.debug_mode then
			# Create the files for dumping ast_sites and model_sites
			sys.dump_ast = new FileWriter.open("{vm.pstats.dir}/dump_ast_sites-{vm.pstats.lbl}.txt")
			sys.dump_object_sites = new FileWriter.open("{vm.pstats.dir}/dump_object_sites-{vm.pstats.lbl}.txt")
		end
	end
end

redef class APropdef
	redef fun compile(vm)
	do
		super
		sys.vm.pstats.nb_ast_sites += object_sites.length

		if sys.debug_mode then
			sys.all_ast_sites.add_all(object_sites)
		end
	end
end

redef class AAttrPropdef
	# When the node encode accessors who are redefined, tell if it's already count as "attr_redef"
	# TODO: maybe remove that, seems useless
	var attr_redef_taken_into = false
end

# Stats of the optimizing model
class MOStats
	# List of analysed sites
	var analysed_sites = new HashSet[MOSite]

	# All the sites which are monomorphics
	var analysed_monomorph_sites = new HashSet[MOSite]

	# List of compiled methods
	var compiled_methods = new List[MPropDef]

	# List of new site compiled
	var compiled_new = new HashSet[MONew]

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

	# Each time a class is explicitly loaded, count the size of its ancestors
	var loaded_superclasses: Int = 0

	# Each time a class is loaded, count the number of its superclasses which introduced attributes
	var loaded_superclasses_attributes: Int = 0

	# All loaded classes in the program
	var loaded_classes = new List[MClass]

	# The number of MOSite with a primitive receiver
	var nb_primitive_sites: Int = 0

	# The general matrix of the statistics
	var matrix: Array[Array[Int]] = new Array[Array[Int]]

	# The directory used to store current results of statistics
	var dir: String is noinit

	# Number of methods execution of each implementation
	var method_static = 0
	var method_sst = 0
	var method_ph = 0

	# Number of attribute execution of each implementation
	var attribute_sst = 0
	var attribute_ph = 0

	# Number of cast execution of each implementation
	var cast_static = 0
	var cast_sst = 0
	var cast_ph = 0

	# The number of executions of monomorphic sites
	var monomorph_method_executions = 0
	var monomorph_attribute_executions = 0
	var monomorph_cast_executions = 0

	# Number of executions for primitive sites
	var primitive_method_executions = 0
	var primitive_attribute_executions = 0
	var primitive_cast_executions = 0

	# The number of site executions
	var monomorph_methods = 0
	var monomorph_attributes = 0
	var monomorph_casts = 0

	init(s: String)
	do
		# Create a directory with the current date to store the results
		var date = new DateTime.now
		dir = "{date.year}{date.month}{date.day}"

		if sys.preexistence_protocol then
			dir += "_preexistence"
		end

		if sys.mixed_protocol then
			dir += "_mixed"
		end

		if not sys.preexistence_protocol and not sys.mixed_protocol then
			dir += "_patching"
		end

		if not "{date.year}{date.month}{date.day}".file_exists then
			dir.mkdir
		end

		if sys.disable_preexistence_extensions then
			lbl = s + "-original"
		else
			lbl = s + "-extend"
		end
	end

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
		var res = new Array[String].with_capacity(77)

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
		res.add("from readsite preexisting,")
		res.add("from readsite non-preexisting,")

		res.add("\ncallers positive cuc,")
		res.add("callers null cuc,")

		# res.add(",")
		res.add("inter procedural return from new,")
		res.add("inter procedural return from other,")
		res.add("from primitive/lit,")
		res.add("procedure,")

		# res.add(",")
		res.add("\nNumber of loaded classes,")
		res.add("Number of unloaded classes,")
		res.add("compiled new of unloaded classes,")

		res.add("\nast sites,")
		res.add("new sites,")
		res.add("object sites,")
		res.add("mo_supers,")
		res.add("primitive_sites,")

		res.add(",")
		res.add("\nprocedures,")
		res.add("methods with a return,")
		res.add("methods with a preexisting return,")
		res.add("methods with a non-preexisting return,")

		res.add(",")
		res.add("preexisting patterns,")
		res.add("non-preexisting patterns with positive cuc,")
		res.add("non-preexisting pattern with null cuc,")
		res.add("no return pattern,")
		res.add("patterns without callees,")
		res.add("not executed patterns,")
		res.add("nb_patterns,")

		# res.add(",")
		res.add("\nsites with preexisting return,")
		res.add("sites with non-preexisting return,")
		res.add("no return sites,")
		res.add("not executed sites,")

		res.add(",")
		res.add("total self receiver,")
		res.add("static self,")
		res.add("sst self,")
		res.add("ph self,")
		res.add("null self,")

		res.add("\n")
		res.add("total from readsite,")
		res.add("readsite with concretes,")
		res.add("static readsite,")
		res.add("sst readsite,")
		res.add("ph readsite,")
		res.add("null readsite,")

		res.add("\nfrom cast,")
		res.add("from cast preexisting,")
		res.add("from cast non-preexisting,")
		return res
	end

	# Print statistics on PICPattern and their implementation
	fun statistics_model
	do
		var file = new FileWriter.open("{dir}/picpatterns-{lbl}.csv")

		# The array to store stats on picpatterns
		var stats_array_size = 4
		var stats_array = new Array[Array[Int]].with_capacity(stats_array_size)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 2)
		end

		var caption_y = new Array[String]
		caption_y.add(",MethodPICPattern, AttributePICPattern\n")
		caption_y.add("total,")
		caption_y.add("sst,")
		caption_y.add("ph,")
		caption_y.add("null,")
		caption_y.add("theoritical bound of pic_patterns,")
		caption_y.add("\n,")

		for pic_pattern in vm.all_picpatterns do
			var impl = pic_pattern.get_impl
			stats_array[0][pic_pattern.index_x] += 1

			if impl isa SSTImpl then
				stats_array[1][pic_pattern.index_x] += 1
			else if impl isa PHImpl then
				stats_array[2][pic_pattern.index_x] += 1
			else if impl isa NullImpl then
				stats_array[3][pic_pattern.index_x] += 1
			end
		end

		stats_array[4][0] = loaded_superclasses
		stats_array[4][1] = loaded_superclasses_attributes

		file.write(caption_y[0])
		for i in [0..stats_array.length[ do
			if i +1< caption_y.length then file.write(caption_y[i+1])
			var size = stats_array[i].length
			for j in [0..size[ do
				file.write(stats_array[i][j].to_s + ",")
			end
			file.write("\n")
		end

		file.close
	end

	fun trace_patterns
	do
		var file = new FileWriter.open("{dir}/trace_patterns-{lbl}.txt")
		var csv_file = new FileWriter.open("{dir}/patterns-{lbl}.csv")

		# The array to store stats on patterns
		var stats_array_size = 7
		var stats_array = new Array[Array[Int]].with_capacity(stats_array_size)
		for i in [0..stats_array_size[ do
			stats_array[i] = new Array[Int].filled_with(0,4)
		end

		# Patterns which have not a unique position between rsc and pic
		var multiple_positions = new HashSet[MOPropSitePattern]

		for pattern in sys.vm.all_patterns do
			file.write("{pattern.trace} {pattern}\n")
			stats_array[0][pattern.index_x] += 1

			var impl = pattern.get_impl(sys.vm)

			if impl isa StaticImpl then
				stats_array[1][pattern.index_x] += 1
			else if impl isa SSTImpl then
				stats_array[2][pattern.index_x] += 1
			else if impl isa PHImpl then
				stats_array[3][pattern.index_x] += 1
			else if impl isa NullImpl then
				stats_array[4][pattern.index_x] += 1
			end

			if pattern.is_monomorphic then
				stats_array[5][pattern.index_x] += 1
			else
				stats_array[6][pattern.index_x] += 1
			end

			# If the pattern has a global property
			if pattern isa MOCallSitePattern then
				var position_rsc = pattern.rsc.get_position_methods(pattern.gp.intro_mclassdef.mclass)

				# Go into the loaded subclasses of this one to check is the position is the same
				for mclass in pattern.rsc.loaded_subclasses do
					if mclass.get_position_methods(pattern.gp.intro_mclassdef.mclass) != position_rsc then
						multiple_positions.add(pattern)
					end
				end
			else if pattern isa MOAttrPattern then
				var position_rsc = pattern.rsc.get_position_attributes(pattern.gp.intro_mclassdef.mclass)

				# Go into the loaded subclasses of this one to check is the position is the same
				for mclass in pattern.rsc.loaded_subclasses do
					if mclass.get_position_attributes(pattern.gp.intro_mclassdef.mclass) != position_rsc then
						multiple_positions.add(pattern)
					end
				end
			end
		end

		# The caption on y axis
		var caption_y = new Array[String]
		caption_y.add(",MOCallSitePattern, MOAttrPattern, MOSubtypeSitePattern, MOAsNotNullPattern\n")
		caption_y.add("total,")
		caption_y.add("static,")
		caption_y.add("sst,")
		caption_y.add("ph,")
		caption_y.add("null,")
		caption_y.add("monomorphic,")
		caption_y.add("polymorphic,")
		caption_y.add("\n,")

		csv_file.write(caption_y[0])
		for i in [0..stats_array.length[ do
			if i +1 < caption_y.length then csv_file.write(caption_y[i+1])

			var size = stats_array[i].length
			for j in [0..size[ do
				csv_file.write(stats_array[i][j].to_s + ",")
			end
			csv_file.write("\n")
		end

		print "multiple_positions {multiple_positions}"
		print "multiple_positions.length {multiple_positions.length}"

		csv_file.close
		file.close
	end

	fun trace_sites
	do
		var file = new FileWriter.open("{dir}/trace_sites-{lbl}.txt")

		print "sys.vm.all_moentities {sys.vm.all_moentities.length + sys.vm.primitive_entities.length}"
		for mosite in sys.vm.all_moentities do
			if mosite isa MOSite then file.write("{mosite.trace} {mosite}\n")

			if sys.debug_mode then
				if mosite.ast != null then
					sys.dump_object_sites.write("{mosite} {mosite.ast.as(not null)}\n")
				else
					sys.debug_file.write("ERROR {mosite} without ast\n")
					sys.dump_object_sites.write("{mosite} null\n")
				end
			end
		end

		var primitives_file = new FileWriter.open("{dir}/trace_primitive_sites-{lbl}.txt")

		# Trace primitive sites
		for mosite in sys.vm.primitive_entities do
			if mosite isa MOSite then primitives_file.write("{mosite.trace} {mosite}\n")
		end

		primitives_file.close

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
		var file = new FileWriter.open("{dir}/trace_local_methods-{lbl}.txt")

		for mpropdef in sys.vm.compiled_mproperties do
			file.write("{mpropdef.trace}\n")
		end

		file.close
	end

	fun trace_global_methods
	do
		var file = new FileWriter.open("{dir}/trace_global_methods-{lbl}.txt")

		for mmethod in sys.vm.compiled_global_methods do
			file.write("{mmethod.trace}\n")
		end

		file.close
	end

	# Make text csv file contains overview statistics
	fun overview
	do
		var file = new FileWriter.open("{dir}/statistics-{lbl}.csv")

		# optimizable_inline: method_preexist_static + attribute_preexist_sst + cast_preexist_static + cast_preexist_sst + null_preexist (total)
		vm.pstats.matrix[19][0] = vm.pstats.matrix[7][0] + vm.pstats.matrix[10][1] + vm.pstats.matrix[7][2] + vm.pstats.matrix[10][2] + vm.pstats.matrix[16][5]

		# non optimizable inline: npreexist_static + attribute_npreexist_sst + cast_npreexist_sst + null_npreexist (total)
		vm.pstats.matrix[20][0] = vm.pstats.matrix[8][5] + vm.pstats.matrix[11][1] + vm.pstats.matrix[11][2] + vm.pstats.matrix[17][5]

		# non_inline: total_ph + method_sst + asnotnull_sst
		vm.pstats.matrix[21][0] = vm.pstats.matrix[12][5] + vm.pstats.matrix[9][0] + vm.pstats.matrix[9][3]

		# cuc: caller uncompiled
		var cuc_pos = 0
		var cuc_null = 0

		var trace_file = new FileWriter.open("{dir}/trace_file-{lbl}.txt")
		var trace_model = new FileWriter.open("{dir}/trace_model-{lbl}.txt")

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
			if propdef.msignature.return_mtype != null and propdef.return_expr != null and not propdef.msignature.return_mtype.is_primitive_type then
				nb_method_return += 1

				# If the propdef has a preexisting return
				if propdef.return_expr.return_preexist.bit_pre then
					nb_method_return_pre += 1
					# Trace the origin of preexistence
					var origin = propdef.return_expr.preexistence_origin

					sys.vm.return_origin[origin] += 1
					sys.vm.return_origin[sys.vm.return_origin.length-1] += 1
				else
					nb_method_return_npre += 1
				end
			else
				nb_procedure += 1
			end
		end

		trace_file.close
		trace_model.close

		vm.pstats.matrix[33][0] = cuc_pos
		vm.pstats.matrix[34][0] = cuc_null

		# compiled "new" of unloaded classes at the end of execution
		var compiled_new_unloaded = 0

		# Loaded classes at the end of execution
		var loaded_classes = new HashSet[MClass]
		var unloaded_classes = new HashSet[MClass]
		for newsite in sys.vm.all_new_sites do
			if not newsite.pattern.cls.abstract_loaded then
				compiled_new_unloaded += 1
				unloaded_classes.add(newsite.pattern.cls)
				print("UNLOADED {newsite} class = {newsite.pattern.cls}")
			else
				loaded_classes.add(newsite.pattern.cls)
			end
		end

		print "Unloaded classes {unloaded_classes}"

		vm.pstats.matrix[39][0] = loaded_classes.length
		vm.pstats.matrix[40][0] = unloaded_classes.length
		vm.pstats.matrix[41][0] = compiled_new_unloaded

		vm.pstats.matrix[42][0] = sys.vm.pstats.nb_ast_sites
		vm.pstats.matrix[43][0] = sys.vm.all_new_sites.length
		vm.pstats.matrix[44][0] = sys.vm.all_moentities.length + sys.vm.primitive_entities.length
		vm.pstats.matrix[45][0] = sys.vm.mo_supers.length
		vm.pstats.matrix[46][0] = sys.vm.primitive_entities.length

		vm.pstats.matrix[48][0] = nb_procedure
		vm.pstats.matrix[49][0] = nb_method_return
		vm.pstats.matrix[50][0] = nb_method_return_pre
		vm.pstats.matrix[51][0] = nb_method_return_npre

		# Print the captions of the statistics file
		for caption in caption_x do
			file.write(caption)
		end

		# Go into each pattern to collect statistics on them
		for pattern in sys.vm.all_patterns do
			# If the pattern is a callsitepattern with a return
			if not pattern.is_executed then
				vm.pstats.matrix[58][pattern.index_x] += 1
			end

			if pattern isa MOCallSitePattern then

				if pattern.callees.length == 0 then
					vm.pstats.matrix[57][0] += 1

					# The pattern has no callees but was executed
					if pattern.is_executed == true then
						# Several possibilities: the receiver static class is not loaded or the global property is a particular method like != or ==
						print "Pattern {pattern.rsc}#{pattern.gp} executed but without callees {pattern.gp.living_mpropdefs}, rsc loaded ? = {pattern.rsc.abstract_loaded}"
					end
				else
					if pattern.gp.intro.msignature.return_mtype == null or pattern.gp.intro.msignature.return_mtype.is_primitive_type then
						vm.pstats.matrix[56][0] += 1
					else
						# A preexisting pattern is a pattern with cuc = 0 and all callees with a preexisting return
						if pattern.is_pre and pattern.cuc == 0 then
							vm.pstats.matrix[53][0] += 1
						else
							if pattern.cuc > 0 then
								vm.pstats.matrix[54][0] += 1
							else
								vm.pstats.matrix[55][0] += 1
							end
						end
					end
				end
			end

			# All patterns are counted here
			vm.pstats.matrix[59][pattern.index_x] += 1
			vm.pstats.matrix[59][5] += 1
		end

		for i in [0..vm.pstats.matrix.length[ do
			# Write the caption on the line if any
			if i < caption_y.length then file.write(caption_y[i])

			# Then print the statistics
			var size = vm.pstats.matrix[i].length
			for j in [0..size[ do
				var value = vm.pstats.matrix[i][j]
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
						print "concrete_receivers"
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

		loaded_classes = counters.loaded_classes
		loaded_superclasses = counters.loaded_superclasses
		loaded_superclasses_attributes = counters.loaded_superclasses_attributes

		analysed_sites.add_all(counters.analysed_sites)
		analysed_monomorph_sites.add_all(counters.analysed_monomorph_sites)
		compiled_methods.add_all(counters.compiled_methods)
		compiled_new.add_all(counters.compiled_new)
		nb_ast_sites = counters.nb_ast_sites

		new_sites = sys.vm.all_new_sites.length
		object_sites = sys.vm.all_moentities.length + sys.vm.primitive_entities.length

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
			vm.pstats.matrix[37][0] += 1
		else
			vm.pstats.matrix[38][0] += 1
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

	# The number of recompilations of this entity
	var recompilations: Int = 0

	var cached_preexistence_value: Int = -1

	# Count the implementation of the site
	fun stats(vm: VirtualMachine)
	do
		# Compute the concrete types of this site
		if not is_monomorph then
			concrete_receivers = null
			compute_concretes_site
		end

		expr_recv.preexist_init
		cached_preexistence_value = site_preexist
		origin = expr_recv.preexistence_origin

		# Increment statistics on callsites
		incr_stats_sites

		if self.is_monomorph then
			if self isa MOCallSite then
				vm.pstats.monomorph_methods += 1
			else if self isa MOAttrSite then
				vm.pstats.monomorph_attributes += 1
			else if self isa MOSubtypeSite then
				vm.pstats.monomorph_casts += 1
			end

			return
		end

		incr_from_site
		incr_concrete_site
		incr_self
		incr_rst_unloaded(vm)

		sys.vm.receiver_origin[origin] += 1
		sys.vm.receiver_origin[sys.vm.receiver_origin.length -1] += 1

		# Trace the origin of preexistence of callsites
		if self isa MOCallSite then
			sys.vm.trace_origin[trace_origin] += 1
			sys.vm.trace_origin[sys.vm.trace_origin.length-1] += 1
		end

		vm.pstats.matrix[get_impl(vm).compute_index_y(self)][index_x] += 1

		# Increment the total for implementation of the previous line
		incr_total
	end

	# Print the pattern (RST/GP or target class for subtype test)
	fun pattern2str: String is abstract

	# Statistics on the return of callsites (call-expressions not necessarily used as a receiver)
	fun incr_stats_sites
	do
		if not self isa MOCallSite then return

		if not is_executed then
			vm.pstats.matrix[63][index_x] += 1
		end

		# If self is a site which returns something
		if self isa MOFunctionSite then
			# The method returns a preexisting value which is not a primitive type
			# If the site is preexisting with concretes receivers for example, the site is preexisting
			if compute_preexist.bit_pre then
				vm.pstats.matrix[60][0] += 1
			else
				# For all other cases, the site is non-preexisting
				vm.pstats.matrix[61][0] += 1
			end
		else
			# A primitive or a real procedure
			vm.pstats.matrix[62][0] += 1
		end
	end

	fun incr_total
	do
		var impl = get_impl(vm)
		var pre = cached_preexistence_value.bit_pre

		if is_primitive or is_monomorph then return
		vm.pstats.matrix[impl.index_y][index_x] += 1
		vm.pstats.matrix[impl.index_y][5] += 1
		vm.pstats.matrix[impl.compute_index_y(self)][5] += 1

		# The total of preexisting sites
		if pre then
			vm.pstats.matrix[1][index_x] += 1
			vm.pstats.matrix[1][5] += 1
		else
			vm.pstats.matrix[2][index_x] += 1
			vm.pstats.matrix[2][5] += 1
		end
	end

	# Trace origins of preexistence
	fun incr_from_site
	do
		# Filter the receiver which come from a parameter or a literal
		if origin == 1 or origin == 8 or origin == 16 or is_primitive or is_monomorph then return
		if origin == 129 or origin == 136 or origin == 144 then return
		if self isa MOAsNotNullSite then return

		# If the receiver comes only from a new
		if origin == 2 or origin == 130 then
			vm.pstats.matrix[23][index_x] += 1
			vm.pstats.matrix[23][5] += 1

			if cached_preexistence_value.bit_pre and not disable_preexistence_extensions then
				vm.pstats.matrix[24][index_x] += 1
				vm.pstats.matrix[24][5] += 1
			else
				vm.pstats.matrix[25][index_x] += 1
				vm.pstats.matrix[25][5] += 1
			end
		else if origin == 4 or origin == 132 then
			# If the receiver comes only from a callsite
			# The total of callsites
			vm.pstats.matrix[26][index_x] += 1
			vm.pstats.matrix[26][5] += 1

			# If the receiver is preexisting
			if cached_preexistence_value.bit_pre and not disable_preexistence_extensions then
				vm.pstats.matrix[27][index_x] += 1
				vm.pstats.matrix[27][5] += 1
			else
				vm.pstats.matrix[28][index_x] += 1
				vm.pstats.matrix[28][5] += 1
			end
		else if origin == 256 or origin == 384 then
			# If the receiver comes only from an attribute read
			readsite_statistics

			if cached_preexistence_value.bit_pre and not disable_preexistence_extensions then
				# Preexisting attribute with concrete types
				vm.pstats.matrix[31][index_x] += 1
				vm.pstats.matrix[31][5] += 1
			else
				vm.pstats.matrix[32][index_x] += 1
				vm.pstats.matrix[32][5] += 1
			end
		else if origin == 512 or origin == 640 then
			# If the receiver comes from a cast
			vm.pstats.matrix[77][index_x] += 1
			vm.pstats.matrix[77][5] += 1

			if cached_preexistence_value.bit_pre and not disable_preexistence_extensions then
				vm.pstats.matrix[78][index_x] += 1
				vm.pstats.matrix[78][5] += 1
			else
				vm.pstats.matrix[79][index_x] += 1
				vm.pstats.matrix[79][5] += 1
			end
		else if cached_preexistence_value.bit_pre and not disable_preexistence_extensions then
			# Other cases, a combination of several origins in extended preexistence (parameters and literals are excluded)
			# If the site is preexisting
			vm.pstats.matrix[29][index_x] += 1
			vm.pstats.matrix[29][5] += 1
		else
			vm.pstats.matrix[30][index_x] += 1
			vm.pstats.matrix[30][5] += 1
		end
	end

	# Increment counters for callsites with concrete receivers
	fun incr_concrete_site
	do
		if concrete_receivers != null then
			# Total of concretes for each category
			vm.pstats.matrix[3][index_x] += 1

			# Total of concretes
			vm.pstats.matrix[3][5] += 1

			# Preexisting and non-preexisting sites with concretes
			if cached_preexistence_value.bit_pre then
				vm.pstats.matrix[4][index_x] += 1
				vm.pstats.matrix[4][5] += 1
			else
				vm.pstats.matrix[5][index_x] += 1
				vm.pstats.matrix[5][5] += 1
			end
		end
	end

	# Output special statistics on receiver which come from a readsite
	fun readsite_statistics
	do
		# The total of site coming from a readsite
		vm.pstats.matrix[71][index_x] += 1
		vm.pstats.matrix[71][5] += 1

		if get_concretes != null then
			vm.pstats.matrix[72][index_x] += 1
			vm.pstats.matrix[72][5] += 1
		end

		var impl = get_impl(sys.vm)
		if impl isa StaticImpl then
			vm.pstats.matrix[73][index_x] += 1
			vm.pstats.matrix[73][5] += 1
		else if impl isa SSTImpl then
			vm.pstats.matrix[74][index_x] += 1
			vm.pstats.matrix[74][5] += 1
		else if impl isa PHImpl then
			vm.pstats.matrix[75][index_x] += 1
			vm.pstats.matrix[75][5] += 1
		else if impl isa NullImpl then
			vm.pstats.matrix[76][index_x] += 1
			vm.pstats.matrix[76][5] += 1
		end
	end

	# Increment counters if the receiver is `self`
	fun incr_self
	do
		if expr_recv isa MOSelf then
			vm.pstats.matrix[0][index_x] += 1
			vm.pstats.matrix[0][5] += 1
		end

		# Recopy the total of self sites
		if expr_recv isa MOSelf then
			vm.pstats.matrix[65][index_x] += 1
			vm.pstats.matrix[65][5] += 1

			# Increment for each implementation with self as a receiver
			var impl = get_impl(sys.vm)
			if impl isa StaticImpl then
				vm.pstats.matrix[66][index_x] += 1
				vm.pstats.matrix[66][5] += 1
			else if impl isa SSTImpl then
				vm.pstats.matrix[67][index_x] += 1
				vm.pstats.matrix[67][5] += 1
			else if impl isa PHImpl then
				vm.pstats.matrix[68][index_x] += 1
				vm.pstats.matrix[68][5] += 1
			else if impl isa NullImpl then
				vm.pstats.matrix[69][index_x] += 1
				vm.pstats.matrix[69][5] += 1
			end
		end
	end

	# Increment counters if the receiver static class is unloaded
	fun incr_rst_unloaded(vm: VirtualMachine)
	do
		var rst_loaded = pattern.rsc.abstract_loaded

		if not rst_loaded then
			var impl = get_impl(vm)

			vm.pstats.matrix[impl.index_y][4] += 1
			vm.pstats.matrix[impl.compute_index_y(self)][4] += 1

			if cached_preexistence_value.bit_pre then
				vm.pstats.matrix[1][4] += 1
			else
				vm.pstats.matrix[2][4] += 1
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
		var res = "{self} recv {expr_recv} "
		if is_monomorph then res += "monomorph "
		if is_conservative then res += "is_conservative "

		if pattern.rsc.is_final then res += "final_rcv = {pattern.rsc} "

		if concrete_receivers != null then
			res += "concretes = {concrete_receivers.as(not null)}"
		else
			res += "concretes = null"
		end

		res += " used impl {get_impl(sys.vm)} conservative_impl {conservative_impl.as(not null)}"

		res += " preexistence {expr_recv.compute_preexist} preexistence_origin {expr_recv.preexistence_origin}"
		res += " executions {executions}"
		res += " recompilations {recompilations}"
		res += " enclosing {lp}"
		res += " pattern_impl {pattern.get_impl(vm)}"

		return res
	end

	redef fun reinit_impl
	do
		super

		recompilations += 1
	end

	# The number of executions of this site
	var executions = 0
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
		return super + " intro_mclass = {pattern.gp.intro_mclassdef.mclass}, {pattern.rsc}#{pattern.gp} is_executed = {is_executed}"
	end
end

redef class PICPattern
	var index_x: Int is noinit

	# The number of recompilations of this entity
	var recompilations: Int = 0

	redef fun reinit_impl
	do
		super

		# Each time a picpattern has a change in its implementation, count it
		recompilations += 1
	end
end

redef class MethodPICPattern
	redef var index_x = 0
end

redef class AttributePICPattern
	redef var index_x = 1
end

redef class MOCallSite
	redef var index_x = 0

	redef var site_type = "method"

	redef fun trace
	do
		var res = " {pattern.rsc}#{pattern.gp}"

		var preexistence_value = compute_preexist
		if preexistence_value.bit_pre then
			res += " return_preexist {preexistence_value}"
		end

		return super + res
	end

	redef fun reinit_impl
	do
		super

		# Each time a pattern has a change in its implementation, count it
		recompilations += 1
	end
end

redef class MOFunctionSite
	redef fun trace
	do
		if compute_concretes(null) != null then
			return super + " returned concretes = {compute_concretes(null).as(not null)}"
		else
			return super
		end
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

	redef fun trace
	do
		var res = " source {pattern.rsc} target {pattern.target_mclass}"

		return super + res
	end
end

redef class MOAsNotNullSite
	redef fun pattern2str do return "{pattern.rst}->not null"

	redef var site_type = "asnotnull"

	redef var index_x = 3
end

redef class MOSitePattern
	var index_x: Int = 5

	# Return true if all sites in this pattern are monomorphic
	fun is_monomorphic: Bool
	do
		var res = true
		for site in sites do
			if not site.is_monomorph then res = false
		end

		return res
	end

	# The number of recompilations of this entity
	var recompilations: Int = 0

	redef fun reinit_impl
	do
		super

		# Each time a pattern has a change in its implementation, count it
		recompilations += 1
	end

	fun trace: String
	do
		return "nb_recompilations {recompilations} executed {is_executed} Pattern {rsc}"
	end
end

redef class MOPropSitePattern

	redef fun trace
	do
		return super + "#{gp} rsc_loaded = {rsc.abstract_loaded} nb_sites {sites.length} impl {get_impl(vm)}"
	end
end

redef class MOCallSitePattern
	redef var index_x = 0

	redef fun trace
	do
		return super + " cuc = {cuc} + nb_callees {callees.length}"
	end
end

redef class MOAttrPattern
	redef var index_x = 1
end

redef class MOSubtypeSitePattern
	redef var index_x = 2

	redef fun trace
	do
		return super + " nb_site {sites.length} target = {target}"
	end
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
		if mosite.cached_preexistence_value.bit_pre then
			return index_y + 1
		else
			return index_y + 2
		end
	end
end

redef class StaticImpl
	redef var index_y = 6
end

redef class StaticImplMethod

	redef fun exec_method(recv)
	do
		if mo_entity.as(MOSite).is_primitive then
			sys.vm.pstats.primitive_method_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_method_executions += 1
		else
			sys.vm.pstats.method_static += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		return super
	end
end

redef class StaticImplSubtype

	redef fun exec_subtype(recv)
	do
		if mo_entity.as(MOSite).is_primitive then
			vm.pstats.primitive_cast_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_cast_executions += 1
		else
			sys.vm.pstats.cast_static += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		return super
	end
end

redef class FinalImplementation

	redef fun exec_subtype(recv)
	do
		if mo_entity.as(MOSite).is_primitive then
			vm.pstats.primitive_cast_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_cast_executions += 1
		else
			sys.vm.pstats.cast_static += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		return super
	end
end

redef class SSTImpl
	redef var index_y = 9

	redef fun exec_attribute_read(recv)
	do
		if mo_entity.as(MOSite).is_primitive then
			vm.pstats.primitive_attribute_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_attribute_executions += 1
		else
			sys.vm.pstats.attribute_sst += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		return super
	end

	redef fun exec_attribute_write(recv, instance)
	do
		if mo_entity.as(MOSite).is_primitive then
			vm.pstats.primitive_attribute_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_attribute_executions += 1
		else
			sys.vm.pstats.attribute_sst += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		super
	end

	redef fun exec_method(recv)
	do
		if mo_entity.as(MOSite).is_primitive then
			vm.pstats.primitive_method_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_method_executions += 1
		else
			sys.vm.pstats.method_sst += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		return super
	end
end

redef class SSTImplSubtype

	redef fun exec_subtype(recv)
	do
		if mo_entity.as(MOSite).is_primitive then
			vm.pstats.primitive_cast_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_cast_executions += 1
		else
			sys.vm.pstats.cast_sst += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		return super
	end
end

redef class PHImpl
	redef var index_y = 12

	redef fun exec_attribute_read(recv)
	do
		if mo_entity.as(MOSite).is_primitive then
			vm.pstats.primitive_attribute_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_attribute_executions += 1
		else
			sys.vm.pstats.attribute_ph += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		return super
	end

	redef fun exec_attribute_write(recv, value)
	do
		if mo_entity.as(MOSite).is_primitive then
			vm.pstats.primitive_attribute_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_attribute_executions += 1
		else
			sys.vm.pstats.attribute_ph += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		super
	end

	redef fun exec_method(recv)
	do
		if mo_entity.as(MOSite).is_primitive then
			vm.pstats.primitive_method_executions += 1
		else if mo_entity.as(MOSite).is_monomorph then
			sys.vm.pstats.monomorph_method_executions += 1
		else
			sys.vm.pstats.method_ph += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		return super
	end

	redef fun exec_subtype(recv)
	do
		if mo_entity.as(MOSite).is_primitive then
			sys.vm.pstats.primitive_cast_executions += 1
		else
			sys.vm.pstats.cast_ph += 1
		end

		mo_entity.as(MOSite).executions += 1

		mo_entity.as(MOSite).set_executed

		return super
	end
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

redef class MClass
	# The number of instances of this class
	var nb_instances: Int = 0

	# This method is called when `current_class` class is moved in virtual table of `self`
	redef fun moved_class_methods(vm, current_class, offset)
	do
		super

		vm.suffixes.add(current_class)
		vm.suffixes_methods.add(current_class)
	end

	# This method is called when `current_class` class is moved in virtual table of `self`
	redef fun moved_class_attributes(vm, current_class, offset)
	do
		super

		vm.suffixes.add(current_class)
		vm.suffixes_attributes.add(current_class)
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
			sys.vm.pstats.analysed_sites.add(site)
		end

		for site in self.monomorph_sites do
			site.stats(vm)
			sys.vm.pstats.analysed_monomorph_sites.add(site)
		end

		for newexpr in self.monews do
			sys.vm.pstats.new_sites += 1
		end

		sys.vm.pstats.compiled_methods.add(self)

		if self isa MMethodDef then
			sys.vm.pstats.get_method_return_origin(self)
		end
	end

	# The number of times the propdef is recompiled
	var nb_recompilations = 0

	# Number of times this method is executed
	var nb_executions = 0

	# Number of times the recompilation flag is set
	var nb_recompilation_flag = 0

	redef fun recompile_sites
	do
		super
		nb_recompilations += 1
	end

	fun trace: String
	do
		var res = "LP {self}, GP {mproperty.intro_mclassdef.mclass}#{mproperty}"
		res += ", nb_sites {mosites.length}, nb_news {monews.length}, nb_callers {callers.length} nb_recompilations {nb_recompilations} recompilation_flag {recompilation} nb_recompilation_flag {nb_recompilation_flag}"
		res += " nb_executions {nb_executions}"
		res += ", recompilations_cost {nb_recompilations * (mosites.length + monomorph_sites.length +1)}"

		if return_expr != null then
			if not return_expr_is_object then return res
			if not self isa MMethodDef then return res

			if not msignature.return_mtype == null then
				res += " return_preexist {return_expr.return_preexist}"

				var mclass_return = msignature.return_mtype.as(not null).get_mclass(vm, self)

				res += " return_type {mclass_return.as(not null)}"
				if mclass_return.is_final then res += ", final_return"
				if msignature.return_mtype.as(not null).is_primitive_type then res += ", primitive_return"

				var return_concretes = compute_concretes(sys.vm)
				if return_concretes != null then res += ", return_concretes {return_concretes}"
			end
		end

		res += " all_immutables {all_immutables} all_conservative_impls {all_conservative_impls}"

		return res
	end

	redef fun recompilation=(o: Bool)
	do
		super(o)

		nb_recompilation_flag += 1
	end
end

redef class MOVar
	# Get the origin of return variable (tell if it comes from a new expression), with inter-procedural analysis
	fun return_stats(mproperty: MProperty)
	do
		var callees = new List[MProperty]
		callees.add(mproperty)
		if trace_origin(self, callees) then
			vm.pstats.matrix[36][0] += 1
		else
			vm.pstats.matrix[37][0] += 1
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
end
