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


# Output the statistics to .tex files
module stats_tex

import stats

redef class MOStats
	redef fun overview
	do
		super

		# A special output to .tex files
		dump_to_tex(lbl)
	end

	# A special output of statistics to a .tex files with several tables
	# `lbl` The label to add in the filename
	private fun dump_to_tex(lbl: String)
	do
		# Make a special directory to put the files
		var dir = "{self.dir}/output_latex"
		dir.mkdir

		table1(new FileWriter.open("{dir}/table1-{lbl}.tex"))

		# Do not generate table2 with extended preexistence
		if sys.disable_preexistence_extensions then
			table2(new FileWriter.open("{dir}/table2-{lbl}.tex"))
		end

		# Do not generate table3 in original preexistence
		if not sys.disable_preexistence_extensions then
			table3(new FileWriter.open("{dir}/table3-{lbl}.tex"))
		end

		table4(new FileWriter.open("{dir}/table4-{lbl}.tex"))

		table6(new FileWriter.open("{dir}/table6-{lbl}.tex"))

		table_self(new FileWriter.open("{dir}/table_self-{lbl}.tex"))

		table_final(new FileWriter.open("{dir}/table_final-{lbl}.tex"))

		table_concrete_receivers(new FileWriter.open("{dir}/table_concrete-{lbl}.tex"))

		table_concrete_attributes(new FileWriter.open("{dir}/table_concrete_attributes-{lbl}.tex"))

		table_concrete_final_attributes(new FileWriter.open("{dir}/table_concrete_final_attributes-{lbl}.tex"))

		table_concrete_callsites(new FileWriter.open("{dir}/table_concrete_callsites-{lbl}.tex"))

		table_concrete_casts(new FileWriter.open("{dir}/table_concrete_casts-{lbl}.tex"))

		table_callsite_receivers(new FileWriter.open("{dir}/table_callsite_receivers-{lbl}.tex"))

		table_casts_receivers(new FileWriter.open("{dir}/table_casts_receivers-{lbl}.tex"))

		table_recompilations(new FileWriter.open("{dir}/table_recompilations-{lbl}.tex"))

		table_recompilations_methods(new FileWriter.open("{dir}/table_recompilations_methods-{lbl}.tex"))

		table_executions(new FileWriter.open("{dir}/table_executions-{lbl}.tex"))

		table_executions_warm(new FileWriter.open("{dir}/table_executions_warm-{lbl}.tex"))

		table_executions_code_patching(new FileWriter.open("{dir}/table_executions_code_patching-{lbl}.tex"))

		table_site_implementations(new FileWriter.open("{dir}/table_implementations-{lbl}.tex"))

		table_site_implementations_simplified(new FileWriter.open("{dir}/table_implementations_simplified-{lbl}.tex"))

		generate_line_methods(new FileWriter.open("{dir}/table_benchmarks_methods-{lbl}.tex"))
		generate_line_attributes(new FileWriter.open("{dir}/table_benchmarks_attributes-{lbl}.tex"))

		table_optimistic_implementations(new FileWriter.open("{dir}/table_optimistic_implementations-{lbl}.tex"))
	end

	private var improvable_methods: Int is noinit

	private var improvable_attributes: Int is noinit

	private var improvable_casts: Int is noinit

	private var total_improvable: Int is noinit

	private var total_pre: Int is noinit

	private var total_npre: Int is noinit

	# Generate a first table in latex format
	# `file` An already opened output file
	private fun table1(file: FileWriter)
	do
		# Table 1: Original preexistence
		file.write("%Table 1\n")

		total_pre = vm.pstats.matrix[1][0] + vm.pstats.matrix[1][1] + vm.pstats.matrix[1][2]
		total_npre = vm.pstats.matrix[2][0] + vm.pstats.matrix[2][1] + vm.pstats.matrix[2][2]

		var primitive_methods = 0
		var primitive_attributes = 0
		var primitive_casts = 0

		for mosite in sys.vm.primitive_entities do
			if mosite isa MOSite then
				if mosite isa MOCallSite then
					primitive_methods += 1
				else if mosite isa MOAttrSite then
					primitive_attributes += 1
				else if mosite isa MOSubtypeSite then
					primitive_casts += 1
				end
			end
		end

		var table1 = "%primitive & {primitive_methods} & {primitive_attributes} & {primitive_casts} & {primitive_methods + primitive_attributes + primitive_casts}\\\\\n"
		table1 += "monomorph & {vm.pstats.monomorph_methods} & {vm.pstats.monomorph_attributes} & {vm.pstats.monomorph_casts} & {vm.pstats.monomorph_methods + vm.pstats.monomorph_attributes + vm.pstats.monomorph_casts}\\\\\n"
		table1 += "\\hline\n"
		table1 += "preexisting & {vm.pstats.matrix[1][0]} & {vm.pstats.matrix[1][1]} & {vm.pstats.matrix[1][2]} & {total_pre}\\\\\n"
		table1 += "non preexisting & {vm.pstats.matrix[2][0]} & {vm.pstats.matrix[2][1]} & {vm.pstats.matrix[2][2]} & {total_npre}\\\\\n"
		table1 += "\\hline\n"
		table1 += "total polymorph & {vm.pstats.matrix[1][0] + vm.pstats.matrix[2][0]} & {vm.pstats.matrix[1][1] + vm.pstats.matrix[2][1]} & {vm.pstats.matrix[1][2] + vm.pstats.matrix[2][2]} & {(total_pre + total_npre)}\\\\\n"
		table1 += "preexistence rate & {vm.pstats.matrix[1][0]*100/(vm.pstats.matrix[1][0] + vm.pstats.matrix[2][0])}\\% & {vm.pstats.matrix[1][1]*100/(vm.pstats.matrix[1][1] + vm.pstats.matrix[2][1])}\\% & {vm.pstats.matrix[1][2]*100/(vm.pstats.matrix[1][2] + vm.pstats.matrix[2][2])}\\% & {total_pre*100/(total_pre + total_npre)}\\%\\\n"

		file.write(table1)
		file.write("\n\n")
		file.close
	end

	# Generate a second table in latex format
	# `file` An already opened output file
	private fun table2(file: FileWriter)
	do
		file.write("%Table 2\n")

		# Line "other",  sites which are not preexisting
		var other_methods = vm.pstats.matrix[30][0]
		var other_attributes = vm.pstats.matrix[30][1]
		var other_casts = vm.pstats.matrix[30][2]
		var total_others = other_methods + other_attributes + other_casts

		var total_from_new = vm.pstats.matrix[23][0] + vm.pstats.matrix[23][1] + vm.pstats.matrix[23][2]
		var total_from_callsite = vm.pstats.matrix[26][0] + vm.pstats.matrix[26][1] + vm.pstats.matrix[26][2]
		var total_from_readsite = vm.pstats.matrix[32][0] + vm.pstats.matrix[32][1] + vm.pstats.matrix[32][2]
		var total_from_cast = vm.pstats.matrix[79][0] + vm.pstats.matrix[79][1] + vm.pstats.matrix[79][2]

		var general_total = total_from_new + total_from_callsite + total_from_readsite + total_from_cast + other_methods + other_attributes + other_casts

		var table2 = "Read & {vm.pstats.matrix[32][0]} & {vm.pstats.matrix[32][1]} & {vm.pstats.matrix[32][2]} & {total_from_readsite} & {total_from_readsite*100/general_total}\\\\\n"
		table2 += "New & {vm.pstats.matrix[23][0]} & {vm.pstats.matrix[23][1]} & {vm.pstats.matrix[23][2]} & {total_from_new} & {total_from_new*100/general_total}\\\\\n"
		table2 += "Call & {vm.pstats.matrix[26][0]} & {vm.pstats.matrix[26][1]} & {vm.pstats.matrix[26][2]} & {total_from_callsite} & {total_from_callsite*100/general_total}\\\\\n"
		table2 += "Cast & {vm.pstats.matrix[79][0]} & {vm.pstats.matrix[79][1]} & {vm.pstats.matrix[79][2]} & {total_from_cast} & {total_from_cast*100/general_total}\\\\\n"
		table2 += "other & {other_methods} & {other_attributes} & {other_casts} & {total_others} & {total_others*100/general_total}\\\\\n"
		table2 += "\\hline\n"

		table2 += "total & {vm.pstats.matrix[23][0] + vm.pstats.matrix[28][0] + vm.pstats.matrix[32][0] + vm.pstats.matrix[79][0] + other_methods} & {vm.pstats.matrix[23][1] + vm.pstats.matrix[28][1] + vm.pstats.matrix[32][1] + vm.pstats.matrix[79][1] + other_attributes} & {vm.pstats.matrix[23][2] + vm.pstats.matrix[28][2] + vm.pstats.matrix[32][2] + vm.pstats.matrix[79][2] + other_casts} & {general_total} & 100\\\\\n"

		file.write(table2)
		file.write("\n\n")
		file.close
	end

	# Generate a third table in latex format
	# Presents number of improved sites with new rules (call, read and new)
	# `file` An already opened output file
	private fun table3(file: FileWriter)
	do
		file.write("%Table 3\n")

		var total_callsites_improved = vm.pstats.matrix[27][0] + vm.pstats.matrix[27][1] + vm.pstats.matrix[27][2]
		var total_callsites_improvable = vm.pstats.matrix[26][0] + vm.pstats.matrix[26][1] + vm.pstats.matrix[26][2]

		var total_readsite_improved = vm.pstats.matrix[31][0] + vm.pstats.matrix[31][1] + vm.pstats.matrix[31][2]
		var total_readsite_improvable = vm.pstats.matrix[32][0] + vm.pstats.matrix[32][1] + vm.pstats.matrix[32][2] + vm.pstats.matrix[31][0] + vm.pstats.matrix[31][1] + vm.pstats.matrix[31][2]

		var total_new_improved = vm.pstats.matrix[24][0] + vm.pstats.matrix[24][1] + vm.pstats.matrix[24][2]
		var total_new_improvable = vm.pstats.matrix[23][0] + vm.pstats.matrix[23][1] + vm.pstats.matrix[23][2]

		var total_other_improved = vm.pstats.matrix[29][0] + vm.pstats.matrix[29][1] + vm.pstats.matrix[29][2]
		var total_other_improvable = vm.pstats.matrix[29][0] + vm.pstats.matrix[29][1] + vm.pstats.matrix[29][2] + vm.pstats.matrix[30][0] + vm.pstats.matrix[30][1] + vm.pstats.matrix[30][2]

		var table3 = "Read & {vm.pstats.matrix[31][0]} & {vm.pstats.matrix[31][1]} & {vm.pstats.matrix[31][2]} & {total_readsite_improved} & {if total_readsite_improvable != 0 then total_readsite_improved*100/total_readsite_improvable else 0}\\\\\n"
		table3 += "New & {vm.pstats.matrix[24][0]} & {vm.pstats.matrix[24][1]} & {vm.pstats.matrix[24][2]} & {total_new_improved} & {if total_new_improvable != 0 then total_new_improved*100/total_new_improvable else 0}\\\\\n"
		table3 += "Call & {vm.pstats.matrix[27][0]} & {vm.pstats.matrix[27][1]} & {vm.pstats.matrix[27][2]}  & {total_callsites_improved} & {total_callsites_improved*100/total_callsites_improvable}\\\\\n"
		table3 += "Cast & {vm.pstats.matrix[78][0]} & {vm.pstats.matrix[78][1]} & {vm.pstats.matrix[78][2]} & {vm.pstats.matrix[78][5]} & {vm.pstats.matrix[78][5]*100/vm.pstats.matrix[77][5]}\\\\\n"
		table3 += "other & {vm.pstats.matrix[29][0]} & {vm.pstats.matrix[29][1]} & {vm.pstats.matrix[29][2]} & {total_other_improved} & {if total_other_improvable != 0 then total_other_improved*100/total_other_improvable else 0}\\\\\n"

		table3 += "\\hline\n"

		var total_improved_method = vm.pstats.matrix[27][0] + vm.pstats.matrix[24][0] + vm.pstats.matrix[29][0] + vm.pstats.matrix[31][0] + vm.pstats.matrix[78][0]
		var total_improvable_method = vm.pstats.matrix[26][0] + vm.pstats.matrix[31][0] + vm.pstats.matrix[23][0] + vm.pstats.matrix[29][0] + vm.pstats.matrix[30][0] + vm.pstats.matrix[32][0] + vm.pstats.matrix[77][2]

		var total_improved_attribute = vm.pstats.matrix[27][1] + vm.pstats.matrix[24][1] + vm.pstats.matrix[29][1] + vm.pstats.matrix[31][1] + vm.pstats.matrix[78][1]
		var total_improvable_attribute = vm.pstats.matrix[26][1] + vm.pstats.matrix[23][1] + vm.pstats.matrix[29][1] + vm.pstats.matrix[30][1] + vm.pstats.matrix[31][1] + vm.pstats.matrix[32][1] + vm.pstats.matrix[77][1]

		var total_improved_cast = vm.pstats.matrix[27][2] + vm.pstats.matrix[24][2] + vm.pstats.matrix[29][2] + vm.pstats.matrix[31][2] + vm.pstats.matrix[78][2]
		var total_improvable_cast = vm.pstats.matrix[26][2] + vm.pstats.matrix[31][2] + vm.pstats.matrix[23][2] + vm.pstats.matrix[29][2] + vm.pstats.matrix[30][2] + vm.pstats.matrix[32][2] + vm.pstats.matrix[77][2]

		var total_table3 = (total_improved_method + total_improved_attribute + total_improved_cast)*100/(total_improvable_method + total_improvable_attribute + total_improvable_cast)
		table3 += "total improved & {total_improved_method} & {total_improved_attribute} & {total_improved_cast} & {total_improved_method + total_improved_attribute + total_improved_cast} & {total_table3}\\\\\n"

		file.write(table3)
		file.write("\n\n")
		file.close
	end

	# Generate a third table with percentages in latex format
	# Presents percentages of improved sites with new rules (call, read and new)
	# `file` An already opened output file
	private fun table3_percentages(file: FileWriter)
	do
		file.write("%Table 3 percentages\n")

		var total_callsites_improved = vm.pstats.matrix[27][0] + vm.pstats.matrix[27][1] + vm.pstats.matrix[27][2]
		var total_callsites_improvable = vm.pstats.matrix[26][0] + vm.pstats.matrix[26][1] + vm.pstats.matrix[26][2]

		var total_readsite_improved = vm.pstats.matrix[31][0] + vm.pstats.matrix[31][1] + vm.pstats.matrix[31][2]
		var total_readsite_improvable = vm.pstats.matrix[31][0] + vm.pstats.matrix[31][1] + vm.pstats.matrix[31][2] + vm.pstats.matrix[32][0] + vm.pstats.matrix[32][1] + vm.pstats.matrix[32][2]

		var total_new_improved = vm.pstats.matrix[24][0] + vm.pstats.matrix[24][1] + vm.pstats.matrix[24][2]
		var total_new_improvable = vm.pstats.matrix[23][0] + vm.pstats.matrix[23][1] + vm.pstats.matrix[23][2]

		var total_other_improved = vm.pstats.matrix[29][0] + vm.pstats.matrix[29][1] + vm.pstats.matrix[29][2]
		var total_other_improvable = vm.pstats.matrix[29][0] + vm.pstats.matrix[29][1] + vm.pstats.matrix[29][2] + vm.pstats.matrix[30][0] + vm.pstats.matrix[30][1] + vm.pstats.matrix[30][2]

		var table3 = "Call & {if vm.pstats.matrix[26][0] != 0 then vm.pstats.matrix[27][0]*100/vm.pstats.matrix[26][0] else 0} & {if vm.pstats.matrix[26][1] != 0 then vm.pstats.matrix[27][1]*100/vm.pstats.matrix[26][1] else 0} & {if vm.pstats.matrix[26][2] != 0 then vm.pstats.matrix[27][2]*100/vm.pstats.matrix[26][2] else 0}  & {total_callsites_improved*100/total_callsites_improvable}\\\\\n"
		table3 += "Read & {if vm.pstats.matrix[31][0] != 0 then vm.pstats.matrix[31][0]*100/(vm.pstats.matrix[31][0] + vm.pstats.matrix[32][0]) else 0} & {if vm.pstats.matrix[31][1] != 0 then vm.pstats.matrix[31][1]*100/(vm.pstats.matrix[31][1] + vm.pstats.matrix[32][1]) else 0} & {if vm.pstats.matrix[31][2] != 0 then vm.pstats.matrix[31][2]*100/(vm.pstats.matrix[31][2] + vm.pstats.matrix[32][2]) else 0} & {if total_readsite_improvable != 0 then total_readsite_improved*100/total_readsite_improvable else 0}\\\\\n"
		table3 += "New & {if vm.pstats.matrix[23][0] != 0 then vm.pstats.matrix[24][0]*100/vm.pstats.matrix[23][0] else 0} & {if vm.pstats.matrix[23][1] != 0 then vm.pstats.matrix[24][1]*100/vm.pstats.matrix[23][1] else 0} & {if vm.pstats.matrix[23][2] != 0 then vm.pstats.matrix[24][2]*100/vm.pstats.matrix[23][2] else 0} & {total_new_improved*100/total_new_improvable}\\\\\n"
		table3 += "Cast & {if vm.pstats.matrix[77][0] != 0 then vm.pstats.matrix[78][0]*100/vm.pstats.matrix[77][0] else 0} & {if vm.pstats.matrix[77][1] != 0 then vm.pstats.matrix[78][1]*100/vm.pstats.matrix[77][1] else 0} & {if vm.pstats.matrix[77][2] != 0 then vm.pstats.matrix[78][2]*100/vm.pstats.matrix[77][2] else 0} & {vm.pstats.matrix[78][5]*100/vm.pstats.matrix[77][5]}\\\\\n"
		table3 += "other & {if vm.pstats.matrix[29][0] != 0 then vm.pstats.matrix[29][0]*100/(vm.pstats.matrix[29][0] + vm.pstats.matrix[30][0]) else 0} & {if vm.pstats.matrix[29][1] != 0 then vm.pstats.matrix[29][1]*100/(vm.pstats.matrix[29][1] + vm.pstats.matrix[30][1]) else 0} & {if vm.pstats.matrix[29][2] != 0 then vm.pstats.matrix[29][2]*100/(vm.pstats.matrix[29][2] + vm.pstats.matrix[30][2]) else 0} & {if total_other_improvable != 0 then total_other_improved*100/total_other_improvable else 0}\\\\\n"

		table3 += "\\hline\n"

		var total_improved_method = vm.pstats.matrix[27][0] + 0 + vm.pstats.matrix[24][0] + vm.pstats.matrix[29][0] + vm.pstats.matrix[78][0]
		var total_improvable_method = vm.pstats.matrix[26][0] + vm.pstats.matrix[31][0] + vm.pstats.matrix[23][0] + vm.pstats.matrix[29][0] + vm.pstats.matrix[30][0] + vm.pstats.matrix[77][0]

		var total_improved_attribute = vm.pstats.matrix[27][1] + 0 + vm.pstats.matrix[24][1] + vm.pstats.matrix[29][1] + vm.pstats.matrix[78][1]
		var total_improvable_attribute = vm.pstats.matrix[26][1] + vm.pstats.matrix[31][1] + vm.pstats.matrix[23][1] + vm.pstats.matrix[29][1] + vm.pstats.matrix[30][1] + vm.pstats.matrix[77][1]

		var total_improved_cast = vm.pstats.matrix[27][2] + 0 + vm.pstats.matrix[24][2] + vm.pstats.matrix[29][2] + vm.pstats.matrix[78][2]
		var total_improvable_cast = vm.pstats.matrix[26][2] + vm.pstats.matrix[31][2] + vm.pstats.matrix[23][2] + vm.pstats.matrix[29][2] + vm.pstats.matrix[30][2] + vm.pstats.matrix[77][2]

		var total_table3 = (total_improved_method + total_improved_attribute + total_improved_cast)*100/(total_improvable_method + total_improvable_attribute + total_improvable_cast)
		table3 += "total improved & {if total_improvable_method != 0 then total_improved_method*100/total_improvable_method else 0} & {0} & { if total_improvable_cast != 0 then total_improved_cast*100/total_improvable_cast else 0} & {total_table3}\\\\\n"

		file.write(table3)
		file.write("\n\n")
		file.close
	end

	# Generate a fourth table in latex format
	# `file` An already opened output file
	private fun table4(file: FileWriter)
	do
		file.write("%Table 4\n")

		var optimizable_inline = vm.pstats.matrix[7][0] + vm.pstats.matrix[16][0] + vm.pstats.matrix[10][1] + vm.pstats.matrix[16][1] + vm.pstats.matrix[7][2] + vm.pstats.matrix[10][2] + vm.pstats.matrix[16][2]
		optimizable_inline += vm.pstats.matrix[8][0] + vm.pstats.matrix[17][0] + vm.pstats.matrix[11][1] + vm.pstats.matrix[17][1] + vm.pstats.matrix[8][2] + vm.pstats.matrix[11][2] + vm.pstats.matrix[17][2]

		var nonoptimizable_inline = vm.pstats.matrix[10][0] + vm.pstats.matrix[11][0] + vm.pstats.matrix[12][0] + vm.pstats.matrix[12][1] + vm.pstats.matrix[12][2]
		var total_table4 = optimizable_inline + nonoptimizable_inline

		var total_preexisting = vm.pstats.matrix[7][0] + vm.pstats.matrix[16][0] + vm.pstats.matrix[10][1] + vm.pstats.matrix[16][1] + vm.pstats.matrix[7][2] + vm.pstats.matrix[10][2] + vm.pstats.matrix[16][2]
		var total_nonpreexisting = vm.pstats.matrix[8][0] + vm.pstats.matrix[17][0] + vm.pstats.matrix[11][1] + vm.pstats.matrix[17][1] + vm.pstats.matrix[8][2] + vm.pstats.matrix[11][2] + vm.pstats.matrix[17][2]

		var table4 = "preexisting & {vm.pstats.matrix[7][0] + vm.pstats.matrix[16][0]} & {vm.pstats.matrix[10][1] + vm.pstats.matrix[16][1]} & {vm.pstats.matrix[7][2] + vm.pstats.matrix[10][2] + vm.pstats.matrix[16][2]} & {total_preexisting} & {total_preexisting.to_i*100/total_table4}\\\\\n"
		table4 += "non preexisting & {vm.pstats.matrix[8][0] + vm.pstats.matrix[17][0]} & {vm.pstats.matrix[11][1] + vm.pstats.matrix[17][1]} & {vm.pstats.matrix[8][2] + vm.pstats.matrix[11][2] + vm.pstats.matrix[17][2]} & {total_nonpreexisting} & {total_nonpreexisting.to_i*100/total_table4}\\\\\n"
		table4 += "\\hline\n"

		table4 += "total inlinable & {vm.pstats.matrix[7][0] + vm.pstats.matrix[16][0] + vm.pstats.matrix[8][0] + vm.pstats.matrix[17][0]} & {vm.pstats.matrix[10][1] + vm.pstats.matrix[16][1] + vm.pstats.matrix[11][1] + vm.pstats.matrix[17][1]} & {vm.pstats.matrix[7][2] + vm.pstats.matrix[10][2] + vm.pstats.matrix[16][2] + vm.pstats.matrix[8][2] + vm.pstats.matrix[11][2] + vm.pstats.matrix[17][2]} & {optimizable_inline} & {optimizable_inline*100/total_table4}\\\\\n"
		table4 += "non-inlinable & {vm.pstats.matrix[10][0] + vm.pstats.matrix[11][0] + vm.pstats.matrix[12][0]} & {vm.pstats.matrix[12][1]} & {vm.pstats.matrix[12][2]} & {nonoptimizable_inline} & {nonoptimizable_inline*100/total_table4}\\\\\\hline\n"
		table4 += "total & {vm.pstats.matrix[7][0] + vm.pstats.matrix[16][0] + vm.pstats.matrix[8][0] + vm.pstats.matrix[17][0] + vm.pstats.matrix[10][0] + vm.pstats.matrix[11][0] + vm.pstats.matrix[12][0]} & {vm.pstats.matrix[10][1] + vm.pstats.matrix[16][1] + vm.pstats.matrix[11][1] + vm.pstats.matrix[17][1] + vm.pstats.matrix[12][1]} & {vm.pstats.matrix[7][2] + vm.pstats.matrix[10][2] + vm.pstats.matrix[16][2] + vm.pstats.matrix[8][2] + vm.pstats.matrix[11][2] + vm.pstats.matrix[17][2] + vm.pstats.matrix[12][2]} & {total_table4} & 100\\\\\n"

		file.write(table4)
		file.write("\n\n")
		file.close
	end

	# Statistics of preexistence by method, pattern and site, for sites with a return (MOCallSite)
	#      | Method | pattern | Site |  as receiver
	# pre  |        |         |      |
	# npre |        |         |      |
	# `file` An already opened output file
	private fun table6(file: FileWriter)
	do
		file.write("%Table 6\n")
		file.write("%Method & Pattern & Site & receiver\n")

		var table6 = "preexisting & {vm.pstats.matrix[50][0]} & {vm.pstats.matrix[53][0]} & {vm.pstats.matrix[60][0]} & {vm.pstats.matrix[27][5] - vm.pstats.matrix[27][3]}\\\\\n"
		table6 += "non preexisting & {vm.pstats.matrix[51][0]} & {vm.pstats.matrix[54][0] + vm.pstats.matrix[55][0]} & {vm.pstats.matrix[61][0]} & {vm.pstats.matrix[28][5] -vm.pstats.matrix[28][3]}\\\\\n"
		table6 += "total & {vm.pstats.matrix[50][0] + vm.pstats.matrix[51][0]} & {vm.pstats.matrix[53][0] + vm.pstats.matrix[54][0] + vm.pstats.matrix[55][0]} & {vm.pstats.matrix[60][0] + vm.pstats.matrix[61][0]} & {vm.pstats.matrix[26][5] - vm.pstats.matrix[26][3]}\\\\\n"
		table6 += "\\hline\n"

		table6 += "preexistence rate & {vm.pstats.matrix[50][0]*100/(vm.pstats.matrix[50][0] + vm.pstats.matrix[51][0])} & {vm.pstats.matrix[53][0]*100/(vm.pstats.matrix[53][0] + vm.pstats.matrix[54][0] + vm.pstats.matrix[55][0])} & {vm.pstats.matrix[60][0]*100/(vm.pstats.matrix[60][0] + vm.pstats.matrix[61][0])} & {(vm.pstats.matrix[27][5] -vm.pstats.matrix[27][3])*100/(vm.pstats.matrix[26][5] - vm.pstats.matrix[26][3])}\\\\\n"

		table6 += "without return & {vm.pstats.matrix[48][0]} & {vm.pstats.matrix[56][0]} & {vm.pstats.matrix[62][0]}\\\\\n"

		file.write(table6)
		file.write("\n\n")
		file.close
	end

	# Statistics of implementation for self receivers
	private fun table_self(file: FileWriter)
	do
		file.write("%Table self\n")

		var table_self = "static & {vm.pstats.matrix[66][0]} & {vm.pstats.matrix[66][1]} & {vm.pstats.matrix[66][2]} & {vm.pstats.matrix[66][5]}\\\\\n"
		table_self += "SST & {vm.pstats.matrix[67][0]} & {vm.pstats.matrix[67][1]} & {vm.pstats.matrix[67][2]} & {vm.pstats.matrix[67][5]} \\\\\n"
		table_self += "PH & {vm.pstats.matrix[68][0]} & {vm.pstats.matrix[68][1]} & {vm.pstats.matrix[68][2]} & {vm.pstats.matrix[68][5]} \\\\\n"

		table_self += "\\hline\n"
		table_self += "total & {vm.pstats.matrix[65][0]} & {vm.pstats.matrix[65][1]} & {vm.pstats.matrix[65][2]} & {vm.pstats.matrix[65][5]}\\\\\n"

		file.write(table_self)
		file.write("\n\n")
		file.close
	end

	# Output statistics in .tex file for site which receiver is a final class
	private fun table_final(file: FileWriter)
	do
		file.write("%Table final: non-monomorphic sites with a receiver typed by a loaded final class\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		# The array to store statistics on final sites
		var stats_array_size = 4
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		for site in sys.vm.pstats.analysed_sites do
			var index_x: Int

			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			# We only count MOSite with a final receiver
			if not site.pattern.rsc.is_final then continue
			if not site.pattern.rsc.loaded then continue

			if site isa MOCallSite then
				index_x = 0
				total_methods += 1
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += 1
			else
				index_x = 2
				total_casts += 1
			end

			var impl = site.get_impl(vm)
			if impl isa StaticImpl then
				stats_array[0][index_x] += 1
				stats_array[0][3] += 1
			else if impl isa SSTImpl then
				stats_array[1][index_x] += 1
				stats_array[1][3] += 1
			else if impl isa PHImpl then
				stats_array[2][index_x] += 1
				stats_array[2][3] += 1
			else if impl isa NullImpl then
				stats_array[3][index_x] += 1
				stats_array[3][3] += 1
			end

			grand_total += 1
		end

		var table = "static & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]}\\\\\n"
		table += "SST & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]} \\\\\n"
		table += "PH & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]} \\\\\n"
		table += "Null & {stats_array[3][0]} & {stats_array[3][1]} & {stats_array[3][2]} & {stats_array[3][3]} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods} & {total_attributes} & {total_casts} & {grand_total}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistics in .tex file for site which receiver has concrete types (final or not)
	private fun table_concrete_receivers(file: FileWriter)
	do
		file.write("%Table concrete receivers: MOSite with concrete receivers (with all rules)\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var stats_array_size = 4
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		for site in sys.vm.pstats.analysed_sites do
			var index_x: Int

			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			site.concrete_receivers = null
			var concretes = site.get_concretes

			# We only count MOSite with a concrete receiver
			if concretes == null then continue

			# Filter to keep only preexisting receivers (loaded concretes)
			if not site.expr_recv.expr_preexist.bit_pre then continue

			if site isa MOCallSite then
				index_x = 0
				total_methods += 1
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += 1
			else
				index_x = 2
				total_casts += 1
			end

			var impl = site.get_impl(vm)
			if index_x != -1 then
				if impl isa StaticImpl then
					stats_array[0][index_x] += 1
					stats_array[0][3] += 1
				else if impl isa SSTImpl then
					stats_array[1][index_x] += 1
					stats_array[1][3] += 1
				else if impl isa PHImpl then
					stats_array[2][index_x] += 1
					stats_array[2][3] += 1
				else if impl isa NullImpl then
					stats_array[3][index_x] += 1
					stats_array[3][3] += 1
				end

				grand_total += 1
			end
		end

		var table = "static & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]}\\\\\n"
		table += "SST & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]} \\\\\n"
		table += "PH & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]} \\\\\n"
		table += "Null & {stats_array[3][0]} & {stats_array[3][1]} & {stats_array[3][2]} & {stats_array[3][3]} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods} & {total_attributes} & {total_casts} & {grand_total}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistics in .tex file for site which receiver is a readsite with concrete types
	private fun table_concrete_attributes(file: FileWriter)
	do
		file.write("%Table concrete receivers: MOSite with concrete receivers which is an attribute with concrete types\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var stats_array_size = 4
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		for site in sys.vm.pstats.analysed_sites do
			var index_x: Int

			var origin = site.expr_recv.preexistence_origin

			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			if site.concrete_receivers == null then continue
			if not (origin == 256 or origin == 384) then continue
			# We only count MOSite with concrete_receivers and a readsite receiver

			if site isa MOCallSite then
				index_x = 0
				total_methods += 1
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += 1
			else
				index_x = 2
				total_casts += 1
			end

			var impl = site.get_impl(vm)
			if index_x != -1 then
				if impl isa StaticImpl then
					stats_array[0][index_x] += 1
					stats_array[0][3] += 1
				else if impl isa SSTImpl then
					stats_array[1][index_x] += 1
					stats_array[1][3] += 1
				else if impl isa PHImpl then
					stats_array[2][index_x] += 1
					stats_array[2][3] += 1
				else if impl isa NullImpl then
					stats_array[3][index_x] += 1
					stats_array[3][3] += 1
				end

				grand_total += 1
			end
		end

		var table = "static & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]}\\\\\n"
		table += "SST & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]} \\\\\n"
		table += "PH & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]} \\\\\n"
		table += "Null & {stats_array[3][0]} & {stats_array[3][1]} & {stats_array[3][2]} & {stats_array[3][3]} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods} & {total_attributes} & {total_casts} & {grand_total}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistics in .tex file for site which receiver is a readsite typed by a final class with concrete types
	private fun table_concrete_final_attributes(file: FileWriter)
	do
		file.write("%Table concrete receivers: MOSite with concrete receivers which is a final attribute with concrete types\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var stats_array_size = 4
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		for site in sys.vm.pstats.analysed_sites do
			var index_x: Int

			var origin = site.expr_recv.preexistence_origin

			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			site.concrete_receivers = null
			var concretes = site.get_concretes

			if concretes == null then continue
			if not (origin == 256 or origin == 384) then continue
			if not site.pattern.rsc.is_final then continue
			# We only count MOSite with concrete_receivers and a readsite receiver typed by a final class

			if site isa MOCallSite then
				index_x = 0
				total_methods += 1
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += 1
			else
				index_x = 2
				total_casts += 1
			end

			var impl = site.get_impl(vm)
			if index_x != -1 then
				if impl isa StaticImpl then
					stats_array[0][index_x] += 1
					stats_array[0][3] += 1
				else if impl isa SSTImpl then
					stats_array[1][index_x] += 1
					stats_array[1][3] += 1
				else if impl isa PHImpl then
					stats_array[2][index_x] += 1
					stats_array[2][3] += 1
				else if impl isa NullImpl then
					stats_array[3][index_x] += 1
					stats_array[3][3] += 1
				end

				grand_total += 1
			end
		end

		var table = "static & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]}\\\\\n"
		table += "SST & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]} \\\\\n"
		table += "PH & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]} \\\\\n"
		table += "Null & {stats_array[3][0]} & {stats_array[3][1]} & {stats_array[3][2]} & {stats_array[3][3]} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods} & {total_attributes} & {total_casts} & {grand_total}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistics in .tex file for site which receiver is a callsite with concrete types
	private fun table_concrete_callsites(file: FileWriter)
	do
		file.write("%Table concrete receivers: concrete types returned by callsites\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var stats_array_size = 4
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		for site in sys.vm.pstats.analysed_sites do
			var index_x: Int

			var origin = site.expr_recv.preexistence_origin

			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			site.concrete_receivers = null
			var concretes = site.get_concretes

			if concretes == null then continue
			if not (origin == 4 or origin == 132) then continue
			# We only count MOSite with concrete_receivers from a callsite

			if site isa MOCallSite then
				index_x = 0
				total_methods += 1
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += 1
			else
				index_x = 2
				total_casts += 1
			end

			var impl = site.get_impl(vm)
			if index_x != -1 then
				if impl isa StaticImpl then
					stats_array[0][index_x] += 1
					stats_array[0][3] += 1
				else if impl isa SSTImpl then
					stats_array[1][index_x] += 1
					stats_array[1][3] += 1
				else if impl isa PHImpl then
					stats_array[2][index_x] += 1
					stats_array[2][3] += 1
				else if impl isa NullImpl then
					stats_array[3][index_x] += 1
					stats_array[3][3] += 1
				end

				grand_total += 1
			end
		end

		var table = "static & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]}\\\\\n"
		table += "SST & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]} \\\\\n"
		table += "PH & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]} \\\\\n"
		table += "Null & {stats_array[3][0]} & {stats_array[3][1]} & {stats_array[3][2]} & {stats_array[3][3]} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods} & {total_attributes} & {total_casts} & {grand_total}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistics in .tex file for site which receiver is a cast with concrete types
	private fun table_concrete_casts(file: FileWriter)
	do
		file.write("%Table concrete from casts: concrete types returned by casts\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var stats_array_size = 4
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		for site in sys.vm.pstats.analysed_sites do
			var index_x: Int

			var origin = site.expr_recv.preexistence_origin

			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			site.concrete_receivers = null
			var concretes = site.get_concretes

			if concretes == null then continue
			if not (origin == 512 or origin == 640) then continue
			# We only count MOSite with concrete_receivers from a callsite

			if site isa MOCallSite then
				index_x = 0
				total_methods += 1
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += 1
			else
				index_x = 2
				total_casts += 1
			end

			var impl = site.get_impl(vm)
			if index_x != -1 then
				if impl isa StaticImpl then
					stats_array[0][index_x] += 1
					stats_array[0][3] += 1
				else if impl isa SSTImpl then
					stats_array[1][index_x] += 1
					stats_array[1][3] += 1
				else if impl isa PHImpl then
					stats_array[2][index_x] += 1
					stats_array[2][3] += 1
				else if impl isa NullImpl then
					stats_array[3][index_x] += 1
					stats_array[3][3] += 1
				end

				grand_total += 1
			end
		end

		var table = "static & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]}\\\\\n"
		table += "SST & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]} \\\\\n"
		table += "PH & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]} \\\\\n"
		table += "Null & {stats_array[3][0]} & {stats_array[3][1]} & {stats_array[3][2]} & {stats_array[3][3]} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods} & {total_attributes} & {total_casts} & {grand_total}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistics in .tex file for site which receiver (possibly an indirectly receiver) is a callsite
	private fun table_callsite_receivers(file: FileWriter)
	do
		file.write("%Table callsite receivers: MOSite with a callsite as a receiver\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var stats_array_size = 4
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		for site in sys.vm.pstats.analysed_sites do
			var index_x: Int

			var origin = site.expr_recv.preexistence_origin

			# We only count callsite receivers
			if not (origin == 4 or origin == 132) then continue

			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			if site isa MOCallSite then
				index_x = 0
				total_methods += 1
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += 1
			else
				index_x = 2
				total_casts += 1
			end

			var impl = site.get_impl(vm)
			if index_x != -1 then
				if impl isa StaticImpl then
					stats_array[0][index_x] += 1
					stats_array[0][3] += 1
				else if impl isa SSTImpl then
					stats_array[1][index_x] += 1
					stats_array[1][3] += 1
				else if impl isa PHImpl then
					stats_array[2][index_x] += 1
					stats_array[2][3] += 1
				else if impl isa NullImpl then
					stats_array[3][index_x] += 1
					stats_array[3][3] += 1
				end

				grand_total += 1
			end
		end

		var table = "static & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]}\\\\\n"
		table += "SST & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]} \\\\\n"
		table += "PH & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]} \\\\\n"
		table += "Null & {stats_array[3][0]} & {stats_array[3][1]} & {stats_array[3][2]} & {stats_array[3][3]} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods} & {total_attributes} & {total_casts} & {grand_total}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistics in .tex file for site which receiver (possibly an indirectly receiver) is a cast
	private fun table_casts_receivers(file: FileWriter)
	do
		file.write("%Table castsites receivers: MOSite with concrete receivers which is a cast\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var stats_array_size = 4
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		for site in sys.vm.pstats.analysed_sites do
			var index_x: Int

			var origin = site.expr_recv.preexistence_origin

			# We only count castsites receivers
			if not (origin == 512 or origin == 640) then continue

			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			if site isa MOCallSite then
				index_x = 0
				total_methods += 1
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += 1
			else
				index_x = 2
				total_casts += 1
			end

			var impl = site.get_impl(vm)
			if index_x != -1 then
				if impl isa StaticImpl then
					stats_array[0][index_x] += 1
					stats_array[0][3] += 1
				else if impl isa SSTImpl then
					stats_array[1][index_x] += 1
					stats_array[1][3] += 1
				else if impl isa PHImpl then
					stats_array[2][index_x] += 1
					stats_array[2][3] += 1
				else if impl isa NullImpl then
					stats_array[3][index_x] += 1
					stats_array[3][index_x] += 1
				end

				grand_total += 1
			end
		end

		var table = "static & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]}\\\\\n"
		table += "SST & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]} \\\\\n"
		table += "PH & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]} \\\\\n"
		table += "Null & {stats_array[3][0]} & {stats_array[3][1]} & {stats_array[3][2]} & {stats_array[3][3]} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods} & {total_attributes} & {total_casts} & {grand_total}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output number of recompilations (i.e. changes in implementations) for each entity of the model
	private fun table_recompilations(file: FileWriter)
	do
		file.write("%Table recompilations: number of recompilations for each entity\n")
		file.write("%Recompilation & Methods & Attributes & Casts & Total\n")

		var stats_array_size = 3
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		for pic_pattern in sys.vm.all_picpatterns do
			var index_x: Int

			if pic_pattern isa MethodPICPattern then
				index_x = 0
			else
				index_x = 1
			end

			stats_array[0][index_x] += pic_pattern.recompilations
			stats_array[0][3] += pic_pattern.recompilations
		end

		for pattern in sys.vm.all_patterns do
			var index_x: Int

			# Do not count as.(not null)
			if pattern isa MOAsNotNullPattern then continue

			if pattern isa MOCallSitePattern then
				index_x = 0
			else if pattern isa MOAttrPattern then
				index_x = 1
			else
				# Casts
				index_x = 2
			end

			stats_array[1][index_x] += pattern.recompilations
			stats_array[1][3] += pattern.recompilations
		end

		for site in sys.vm.pstats.analysed_sites do
			var index_x: Int
			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			if site isa MOCallSite then
				index_x = 0
			else if site isa MOAttrSite then
				index_x = 1
			else
				index_x = 2
			end

			stats_array[2][index_x] += site.recompilations
			stats_array[2][3] += site.recompilations
		end

		for site in sys.vm.pstats.analysed_monomorph_sites do
			var index_x: Int
			# Do not count as.(not null)
			if site isa MOAsNotNullSite then continue

			if site isa MOCallSite then
				index_x = 0
			else if site isa MOAttrSite then
				index_x = 1
			else
				index_x = 2
			end

			stats_array[2][index_x] += site.recompilations
			stats_array[2][3] += site.recompilations
		end

		var table = "PICPattern & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]}\\\\\n"
		table += "GPPattern & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]}\\\\\n"
		table += "Site & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output the number of methods's recompilations
	private fun	table_recompilations_methods(file: FileWriter)
	do
		file.write("%Table recompilations methods: number of times a whole method is recompiled\n")
		file.write("%Compilations & Recompilations \n")

		var recompilations = 0
		var recompilations_cost = 0
		for method in vm.pstats.compiled_methods do
			recompilations += method.nb_recompilations
			recompilations_cost += method.nb_recompilations * (method.mosites.length + method.monomorph_sites.length +1)
		end

		var compilation_cost = vm.pstats.compiled_methods.length + (sys.vm.pstats.analysed_sites.length + sys.vm.pstats.analysed_monomorph_sites.length)

		var table = "number & {vm.pstats.compiled_methods.length} & {recompilations} \\\\\n"
		table += "cost & {compilation_cost} & {recompilations_cost} \\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistic in .tex files for dynamic executions of sites
	private fun table_executions(file: FileWriter)
	do
		file.write("%Table number of execution\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var total_methods = vm.pstats.method_ph + vm.pstats.method_sst + vm.pstats.method_static + vm.pstats.monomorph_method_executions
		var total_attributes = vm.pstats.attribute_ph + vm.pstats.attribute_sst + vm.pstats.monomorph_attribute_executions
		var total_casts = vm.pstats.cast_ph + vm.pstats.cast_sst + vm.pstats.cast_static + vm.pstats.monomorph_cast_executions
		var grand_total = total_methods + total_attributes + total_casts

		var total_primitive = vm.pstats.primitive_method_executions + vm.pstats.primitive_attribute_executions + vm.pstats.primitive_cast_executions

		var table = "%primitive & {vm.pstats.primitive_method_executions/1000} & {vm.pstats.primitive_attribute_executions/1000} & {vm.pstats.primitive_cast_executions/1000} & {total_primitive/1000}\\\\\n"
		table += "monomorph & {vm.pstats.monomorph_method_executions/1000} & {vm.pstats.monomorph_attribute_executions/1000} & {vm.pstats.monomorph_cast_executions/1000} & {vm.pstats.monomorph_method_executions/1000 + vm.pstats.monomorph_attribute_executions/1000 + vm.pstats.monomorph_cast_executions/1000}\\\\\n"
		table += "static & {vm.pstats.method_static/1000} & {0/1000} & {vm.pstats.cast_static/1000} & {vm.pstats.method_static/1000 + vm.pstats.cast_static/1000}\\\\\n"
		table += "SST & {vm.pstats.method_sst/1000} & {vm.pstats.attribute_sst/1000} & {vm.pstats.cast_sst/1000} & {vm.pstats.method_sst/1000 + vm.pstats.attribute_sst/1000 + vm.pstats.cast_sst/1000} \\\\\n"
		table += "PH & {vm.pstats.method_ph/1000} & {vm.pstats.attribute_ph/1000} & {vm.pstats.cast_ph/1000} & {vm.pstats.method_ph/1000 + vm.pstats.attribute_ph/1000 + vm.pstats.cast_ph/1000} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods/1000} & {total_attributes/1000} & {total_casts/1000} & {grand_total/1000}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistic in .tex files for dynamic executions of sites with a counter in each site,
	# it is kind of equivalent to let the vm warm then relaunch the program
	private fun table_executions_warm(file: FileWriter)
	do
		file.write("%Table number of execution warm\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		var stats_array_size = 3
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_primitive_methods = 0
		var total_primitive_attribute = 0
		var total_primitive_casts = 0

		for site in sys.vm.primitive_entities do
			if site isa MOCallSite then
				total_primitive_methods += site.executions
			else if site isa MOAttrSite then
				total_primitive_attribute += site.executions
			else if site isa MOSubtypeSite then
				total_primitive_casts += site.executions
			end
		end

		for site in sys.vm.all_moentities do
			var index_x: Int = -1

			if not site isa MOSite then continue
			if site.is_monomorph then continue
			if site.is_primitive then continue

			if site isa MOCallSite then
				index_x = 0
				total_methods += site.executions
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += site.executions
			else if site isa MOSubtypeSite then
				# Casts
				index_x = 2
				total_casts += site.executions
			end

			grand_total += site.executions

			var impl = site.get_impl(vm)
			if index_x != -1 then
				if impl isa StaticImpl then
					stats_array[1][index_x] += site.executions
					stats_array[1][3] += site.executions
				else if impl isa SSTImpl then
					stats_array[2][index_x] += site.executions
					stats_array[2][3] += site.executions
				else if impl isa PHImpl then
					stats_array[3][index_x] += site.executions
					stats_array[3][3] += site.executions
				end
			end
		end

		var callsite_executions = 0
		var attribute_executions = 0
		var cast_executions = 0

		# Monomorphic sites
		for site in sys.vm.all_moentities do
			if not site isa MOSite then continue
			if not site.is_monomorph then continue

			if site isa MOCallSite then
				total_methods += site.executions
				callsite_executions += site.executions
			else if site isa MOAttrSite then
				total_attributes += site.executions
				attribute_executions += site.executions
			else if site isa MOSubtypeSite then
				# Casts
				total_casts += site.executions
				cast_executions += site.executions
			end

			grand_total += site.executions
		end

		var table = "%primitive & {total_primitive_methods/1000} & {total_primitive_attribute/1000} & {total_primitive_casts/1000} & {total_primitive_methods/1000 + total_primitive_attribute/1000 + total_primitive_casts/1000}\\\\\n"
		table += "monomorph & {callsite_executions/1000} & {attribute_executions/1000} & {cast_executions/1000} & {callsite_executions/1000 + attribute_executions/1000 + cast_executions/1000}\\\\\n"
		table += "static & {stats_array[1][0]/1000} & {stats_array[1][1]/1000} & {stats_array[1][2]/1000} & {stats_array[1][3]/1000} \\\\\n"
		table += "SST & {stats_array[2][0]/1000} & {stats_array[2][1]/1000} & {stats_array[2][2]/1000} & {stats_array[2][3]/1000} \\\\\n"
		table += "PH & {stats_array[3][0]/1000} & {stats_array[3][1]/1000} & {stats_array[3][2]/1000} & {stats_array[3][3]/1000} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods/1000} & {total_attributes/1000} & {total_casts/1000} & {grand_total/1000}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistic in .tex files for dynamic executions of sites with a counter in each site,
	# with code-patching for callsites which can be static, otherwise the preexistence is considered
	private fun table_executions_code_patching(file: FileWriter)
	do
		file.write("%Table number of execution with code-patching for callsites and preexistence\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var total_methods = 0
		var total_attributes = 0
		var total_casts = 0
		var grand_total = 0

		var stats_array_size = 3
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		var total_primitive_methods = 0
		var total_primitive_attribute = 0
		var total_primitive_casts = 0

		for site in sys.vm.primitive_entities do
			if site isa MOCallSite then
				total_primitive_methods += site.executions
			else if site isa MOAttrSite then
				total_primitive_attribute += site.executions
			else if site isa MOSubtypeSite then
				total_primitive_casts += site.executions
			end
		end

		for site in sys.vm.all_moentities do
			var index_x: Int = -1

			if not site isa MOSite then continue
			if site.is_monomorph then continue
			if site.is_primitive then continue

			if site isa MOCallSite then
				index_x = 0
				total_methods += site.executions
			else if site isa MOAttrSite then
				index_x = 1
				total_attributes += site.executions
			else if site isa MOSubtypeSite then
				# Casts
				index_x = 2
				total_casts += site.executions
			end

			grand_total += site.executions

			var impl = site.get_impl(vm)
			if index_x != -1 then
				if (site isa MOCallSite and site.can_be_static) or impl isa StaticImpl then
					stats_array[1][index_x] += site.executions
					stats_array[1][3] += site.executions
				else if impl isa SSTImpl then
					stats_array[2][index_x] += site.executions
					stats_array[2][3] += site.executions
				else if impl isa PHImpl then
					stats_array[3][index_x] += site.executions
					stats_array[3][3] += site.executions
				end
			end
		end

		var callsite_executions = 0
		var attribute_executions = 0
		var cast_executions = 0

		# Monomorphic sites
		for site in sys.vm.all_moentities do
			if not site isa MOSite then continue
			if not site.is_monomorph then continue

			if site isa MOCallSite then
				total_methods += site.executions
				callsite_executions += site.executions
			else if site isa MOAttrSite then
				total_attributes += site.executions
				attribute_executions += site.executions
			else if site isa MOSubtypeSite then
				# Casts
				total_casts += site.executions
				cast_executions += site.executions
			end

			grand_total += site.executions
		end

		var table = "%primitive & {total_primitive_methods/1000} & {total_primitive_attribute/1000} & {total_primitive_casts/1000} & {total_primitive_methods/1000 + total_primitive_attribute/1000 + total_primitive_casts/1000}\\\\\n"
		table += "monomorph & {callsite_executions/1000} & {attribute_executions/1000} & {cast_executions/1000} & {callsite_executions/1000 + attribute_executions/1000 + cast_executions/1000}\\\\\n"
		table += "static & {stats_array[1][0]/1000} & {stats_array[1][1]/1000} & {stats_array[1][2]/1000} & {stats_array[1][3]/1000} \\\\\n"
		table += "SST & {stats_array[2][0]/1000} & {stats_array[2][1]/1000} & {stats_array[2][2]/1000} & {stats_array[2][3]/1000} \\\\\n"
		table += "PH & {stats_array[3][0]/1000} & {stats_array[3][1]/1000} & {stats_array[3][2]/1000} & {stats_array[3][3]/1000} \\\\\n"
		table += "\\hline\n"
		table += "total & {total_methods/1000} & {total_attributes/1000} & {total_casts/1000} & {grand_total/1000}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output statistics about MOSites and their implementations
	private fun table_site_implementations(file: FileWriter)
	do
		file.write("%Table optimistic implementations of sites\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var primitive_methods = 0
		var primitive_attributes = 0
		var primitive_casts = 0

		for mosite in sys.vm.primitive_entities do
			if mosite isa MOSite then
				if mosite isa MOCallSite then
					primitive_methods += 1
				else if mosite isa MOAttrSite then
					primitive_attributes += 1
				else if mosite isa MOSubtypeSite then
					primitive_casts += 1
				end
			end
		end

		var table = "%primitive & {primitive_methods} & {primitive_attributes} & {primitive_casts} & {primitive_methods + primitive_attributes + primitive_casts}\\\\\n"
		table += "monomorph & {vm.pstats.monomorph_methods} & {vm.pstats.monomorph_attributes} & {vm.pstats.monomorph_casts} & {vm.pstats.monomorph_methods + vm.pstats.monomorph_attributes + vm.pstats.monomorph_casts}\\\\\n"
		table += "static & {vm.pstats.matrix[6][0]} & {vm.pstats.matrix[6][1]} & {vm.pstats.matrix[6][2]} & {vm.pstats.matrix[6][0] + vm.pstats.matrix[6][1] + vm.pstats.matrix[6][2]}\\\\\n"
		table += "static preexisting & {vm.pstats.matrix[7][0]} & {vm.pstats.matrix[7][1]} & {vm.pstats.matrix[7][2]} & {vm.pstats.matrix[7][0] + vm.pstats.matrix[7][1] + vm.pstats.matrix[7][2]}\\\\\n"
		table += "static non-preexisting & {vm.pstats.matrix[8][0]} & {vm.pstats.matrix[8][1]} & {vm.pstats.matrix[8][2]} & {vm.pstats.matrix[8][0] + vm.pstats.matrix[8][1] + vm.pstats.matrix[8][2]}\\\\\n"

		table += "SST & {vm.pstats.matrix[9][0]} & {vm.pstats.matrix[9][1]} & {vm.pstats.matrix[9][2]} & {vm.pstats.matrix[9][0] + vm.pstats.matrix[9][1] + vm.pstats.matrix[9][2]} \\\\\n"
		table += "SST preexisting & {vm.pstats.matrix[10][0]} & {vm.pstats.matrix[10][1]} & {vm.pstats.matrix[10][2]} & {vm.pstats.matrix[10][0] + vm.pstats.matrix[10][1] + vm.pstats.matrix[10][2]} \\\\\n"
		table += "SST non-preexisting & {vm.pstats.matrix[11][0]} & {vm.pstats.matrix[11][1]} & {vm.pstats.matrix[11][2]} & {vm.pstats.matrix[11][0] + vm.pstats.matrix[11][1] + vm.pstats.matrix[11][2]} \\\\\n"

		table += "PH & {vm.pstats.matrix[12][0]} & {vm.pstats.matrix[12][1]} & {vm.pstats.matrix[12][2]} & {vm.pstats.matrix[12][0] + vm.pstats.matrix[12][1] + vm.pstats.matrix[12][2]} \\\\\n"
		table += "PH preexisting & {vm.pstats.matrix[13][0]} & {vm.pstats.matrix[13][1]} & {vm.pstats.matrix[13][2]} & {vm.pstats.matrix[13][0] + vm.pstats.matrix[13][1] + vm.pstats.matrix[13][2]} \\\\\n"
		table += "PH non-preexisting & {vm.pstats.matrix[14][0]} & {vm.pstats.matrix[14][1]} & {vm.pstats.matrix[14][2]} & {vm.pstats.matrix[14][0] + vm.pstats.matrix[14][1] + vm.pstats.matrix[14][2]} \\\\\n"

		table += "Null & {vm.pstats.matrix[15][0]} & {vm.pstats.matrix[15][1]} & {vm.pstats.matrix[15][2]} & {vm.pstats.matrix[15][0] + vm.pstats.matrix[15][1] + vm.pstats.matrix[15][2]} \\\\\n"
		table += "Null preexisting & {vm.pstats.matrix[16][0]} & {vm.pstats.matrix[16][1]} & {vm.pstats.matrix[16][2]} & {vm.pstats.matrix[16][0] + vm.pstats.matrix[16][1] + vm.pstats.matrix[16][2]} \\\\\n"
		table += "Null non-preexisting & {vm.pstats.matrix[17][0]} & {vm.pstats.matrix[17][1]} & {vm.pstats.matrix[17][2]} & {vm.pstats.matrix[17][0] + vm.pstats.matrix[17][1] + vm.pstats.matrix[17][2]} \\\\\n"

		table += "\\hline\n"
		table += "total & {vm.pstats.matrix[6][0] + vm.pstats.matrix[9][0] + vm.pstats.matrix[12][0] + vm.pstats.matrix[15][0]} & {vm.pstats.matrix[6][1] + vm.pstats.matrix[9][1] + vm.pstats.matrix[12][1] + vm.pstats.matrix[15][1]} & {vm.pstats.matrix[6][2] + vm.pstats.matrix[9][2] + vm.pstats.matrix[12][2] + vm.pstats.matrix[15][2]} & {vm.pstats.matrix[1][0] + vm.pstats.matrix[2][0] + vm.pstats.matrix[1][1] + vm.pstats.matrix[2][1] + vm.pstats.matrix[1][2] + vm.pstats.matrix[2][2]}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Statistics on optimistic or conservative implementations of sites
	fun table_optimistic_implementations(file: FileWriter)
	do
		file.write("%Table optimistic and conservative implementations of sites\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var primitive_methods = 0
		var primitive_attributes = 0
		var primitive_casts = 0

		var stats_array_size = 3
		var stats_array = new Array[Array[Int]].with_capacity(4)
		for i in [0..stats_array_size] do
			stats_array[i] = new Array[Int].filled_with(0, 4)
		end

		for site in sys.vm.all_moentities do
			var index_x: Int = -1

			if not site isa MOSite then continue
			if site.is_monomorph then continue
			if site.is_primitive then continue

			var impl = site.get_impl(vm)

			# A conservative implementation is used
			if site.is_conservative then
				if site isa MOCallSite then
					if impl isa StaticImplMethod then
						# Conservative optimized
						stats_array[0][0] += 1
						stats_array[0][3] += 1
					else
						stats_array[1][0] += 1
						stats_array[1][3] += 1
					end
				else if site isa MOAttrSite then
					if impl isa SSTImpl then
						# Conservative optimized
						stats_array[0][1] += 1
						stats_array[0][3] += 1
					else
						stats_array[1][1] += 1
						stats_array[1][3] += 1
					end
				else if site isa MOSubtypeSite then
					if impl isa StaticImplSubtype then
						# Conservative optimized
						stats_array[0][2] += 1
						stats_array[0][3] += 1
					else
						stats_array[1][2] += 1
						stats_array[1][3] += 1
					end
				end
			else
				# An optimistic implementation is used
				if site isa MOCallSite then
					if impl isa StaticImplMethod then
						stats_array[2][0] += 1
						stats_array[2][3] += 1
					else
						stats_array[3][0] += 1
						stats_array[3][3] += 1
					end
				else if site isa MOAttrSite then
					if impl isa SSTImpl then
						stats_array[2][1] += 1
						stats_array[2][3] += 1
					else
						stats_array[3][1] += 1
						stats_array[3][3] += 1
					end
				else if site isa MOSubtypeSite then
					if impl isa StaticImplSubtype then
						stats_array[2][2] += 1
						stats_array[2][3] += 1
					else
						stats_array[3][2] += 1
						stats_array[3][3] += 1
					end
				end
			end
		end

		# Primitive and monomorphic sites are excluded

		var table = "Optimal conservative & {stats_array[0][0]} & {stats_array[0][1]} & {stats_array[0][2]} & {stats_array[0][3]} \\\\\n"
		table += "Non-optimized conservative & {stats_array[1][0]} & {stats_array[1][1]} & {stats_array[1][2]} & {stats_array[1][3]} \\\\\n"
		table += "Optimal optimistic & {stats_array[2][0]} & {stats_array[2][1]} & {stats_array[2][2]} & {stats_array[2][3]} \\\\\n"
		table +=
		table += "Non-optimized optimistic & {stats_array[3][0]} & {stats_array[3][1]} & {stats_array[3][2]} & {stats_array[3][3]} \\\\\n"

		var total1 = stats_array[0][0] + stats_array[1][0] + stats_array[2][0] + stats_array[3][0]
		var total2 = stats_array[0][1] + stats_array[1][1] + stats_array[2][1] + stats_array[3][1]
		var total3 = stats_array[0][2] + stats_array[1][2] + stats_array[2][2] + stats_array[3][2]

		table += "\\hline\n"
		table += "total & {total1} & {total2} & {total3} & {total1 + total2 + total3} \\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Output simplified statistics about MOSites and their implementations
	private fun table_site_implementations_simplified(file: FileWriter)
	do
		file.write("%Table simplified implementations of sites\n")
		file.write("% Methods & Attributes & Casts & Total\n")

		var primitive_methods = 0
		var primitive_attributes = 0
		var primitive_casts = 0

		for mosite in sys.vm.primitive_entities do
			if mosite isa MOSite then
				if mosite isa MOCallSite then
					primitive_methods += 1
				else if mosite isa MOAttrSite then
					primitive_attributes += 1
				else if mosite isa MOSubtypeSite then
					primitive_casts += 1
				end
			end
		end

		var polymorph_methods = vm.pstats.matrix[6][0] + vm.pstats.matrix[9][0] + vm.pstats.matrix[12][0]
		var polymorph_attributes = vm.pstats.matrix[6][1] + vm.pstats.matrix[9][1] + vm.pstats.matrix[12][1]
		var polymorph_casts = vm.pstats.matrix[6][2] + vm.pstats.matrix[9][2] + vm.pstats.matrix[12][2]

		var table = "%primitive & {primitive_methods} & {primitive_attributes} & {primitive_casts} & {primitive_methods + primitive_attributes + primitive_casts}\\\\\n"
		table += "monomorph & {vm.pstats.monomorph_methods} & {vm.pstats.monomorph_attributes} & {vm.pstats.monomorph_casts} & {vm.pstats.monomorph_methods + vm.pstats.monomorph_attributes + vm.pstats.monomorph_casts}\\\\\n"
		table += "static & {vm.pstats.matrix[6][0]} & {vm.pstats.matrix[6][1]} & {vm.pstats.matrix[6][2]} & {vm.pstats.matrix[6][0] + vm.pstats.matrix[6][1] + vm.pstats.matrix[6][2]}\\\\\n"
		table += "SST & {vm.pstats.matrix[9][0]} & {vm.pstats.matrix[9][1]} & {vm.pstats.matrix[9][2]} & {vm.pstats.matrix[9][0] + vm.pstats.matrix[9][1] + vm.pstats.matrix[9][2]} \\\\\n"
		table += "PH & {vm.pstats.matrix[12][0]} & {vm.pstats.matrix[12][1]} & {vm.pstats.matrix[12][2]} & {vm.pstats.matrix[12][0] + vm.pstats.matrix[12][1] + vm.pstats.matrix[12][2]} \\\\\n"

		table += "\\hline\n"
		table += "total & {polymorph_methods} & {polymorph_attributes} & {polymorph_casts} & {polymorph_methods + polymorph_attributes + polymorph_casts}\\\\\n"

		file.write(table)
		file.write("\n\n")
		file.close
	end

	# Generate a line per execution (extended or original) with a summary of data
	private fun generate_line_methods(file: FileWriter)
	do
		file.write("%Table summary of benchmarks for methods\n")
		file.write("%Benchmark & original & extended & improvement\n")

		# Original mode
		if sys.disable_preexistence_extensions then
			file.write("{sys.program_name} & {vm.pstats.matrix[7][0]} & \\\\\n")
		else
			file.write("{sys.program_name} & & {vm.pstats.matrix[7][0]} \\\\\n")
		end

		file.write("\n\n")
		file.close
	end

	# Generate a line per execution (extended or original) with a summary of data
	private fun generate_line_attributes(file: FileWriter)
	do
		file.write("%Table summary of benchmarks for attributes\n")
		file.write("%Benchmark & original & extended & improvement\n")

		# Original mode
		if sys.disable_preexistence_extensions then
			file.write("{sys.program_name} & {vm.pstats.matrix[10][1]} & \\\\\n")
		else
			file.write("{sys.program_name} & & {vm.pstats.matrix[10][1]} \\\\\n")
		end

		print sys.program_args

		for arg in program_args do
			if arg.search("[a-zA-Z]*\.nit") != null then
				# Extract the program name
				print arg.search("[a-zA-Z_]*\.nit").as(not null)
			end
		end
		file.write("\n\n")
		file.close
	end
end
