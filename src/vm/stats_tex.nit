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
		var dir = "output_latex"
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

		total_pre = pstats.matrix[1][0] + pstats.matrix[1][1] + pstats.matrix[1][2]
		total_npre = pstats.matrix[2][0] + pstats.matrix[2][1] + pstats.matrix[2][2]

		var table1 = "preexisting & {pstats.matrix[1][0]} & {pstats.matrix[1][1]} & {pstats.matrix[1][2]} & {total_pre}\\\\\n"
		table1 += "non preexisting & {pstats.matrix[2][0]} & {pstats.matrix[2][1]} & {pstats.matrix[2][2]} & {total_npre}\\\\\n"
		table1 += "\\hline\n"
		table1 += "total & {pstats.matrix[1][0] + pstats.matrix[2][0]} & {pstats.matrix[1][1] + pstats.matrix[2][1]} & {pstats.matrix[1][2] + pstats.matrix[2][2]} & {(total_pre + total_npre)}\\\\\n"
		table1 += "preexistence rate & {pstats.matrix[1][0]*100/(pstats.matrix[1][0] + pstats.matrix[2][0])}\\% & {pstats.matrix[1][1]*100/(pstats.matrix[1][1] + pstats.matrix[2][1])}\\% & {pstats.matrix[1][2]*100/(pstats.matrix[1][2] + pstats.matrix[2][2])}\\% & {total_pre*100/(total_pre + total_npre)}\\%\n"

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
		var other_methods = pstats.matrix[29][0] + pstats.matrix[30][0]
		var other_attributes = pstats.matrix[29][1] + pstats.matrix[30][1]
		var other_casts = pstats.matrix[29][2] + pstats.matrix[30][2]
		var total_others = other_methods + other_attributes + other_casts

		var total_from_new = pstats.matrix[23][0] + pstats.matrix[23][1] + pstats.matrix[23][2]
		var total_from_callsite = pstats.matrix[28][0] + pstats.matrix[28][1] + pstats.matrix[28][2]
		var total_from_readsite = pstats.matrix[31][0] + pstats.matrix[31][1] + pstats.matrix[31][2]

		var general_total = total_from_new + total_from_callsite + total_from_readsite + other_methods + other_attributes + other_casts

		var table2 = "ReadSite & {pstats.matrix[31][0]} & {pstats.matrix[31][1]} & {pstats.matrix[31][2]} & {total_from_readsite} & {total_from_readsite*100/general_total}\\\\\n"
		table2 += "NewSite & {pstats.matrix[23][0]} & {pstats.matrix[23][1]} & {pstats.matrix[23][2]} & {total_from_new} & {total_from_new*100/general_total}\\\\\n"
		table2 += "CallSite & {pstats.matrix[28][0]} & {pstats.matrix[28][1]} & {pstats.matrix[28][2]} & {total_from_callsite} & {total_from_callsite*100/general_total}\\\\\n"
		table2 += "other & {other_methods} & {other_attributes} & {other_casts} & {total_others} & {total_others*100/general_total}\\\\\n"
		table2 += "\\hline\n"

		improvable_methods = pstats.matrix[28][0] + other_methods
		improvable_attributes = pstats.matrix[28][1] + other_attributes
		improvable_casts = pstats.matrix[28][2] + other_casts
		total_improvable = improvable_methods + improvable_attributes + improvable_casts

		table2 += "%improvable total & {improvable_methods} & {improvable_attributes} & {improvable_casts} & {total_improvable} & {total_improvable*100/general_total}\\\\\n"

		table2 += "total & {pstats.matrix[23][0] + pstats.matrix[28][0] + pstats.matrix[31][0] + other_methods} & {pstats.matrix[23][1] + pstats.matrix[28][1] + pstats.matrix[31][1] + other_attributes} & {pstats.matrix[23][2] + pstats.matrix[28][2] + pstats.matrix[31][2] + other_casts} & {general_total} & 100\\\\\n"

		file.write(table2)
		file.write("\n\n")
		file.close
	end

	# Generate a third table in latex format
	# Presents the percentage of improved site with new rules (call, read and new)
	# `file` An already opened output file
	private fun table3(file: FileWriter)
	do
		file.write("%Table 3\n")

		var total_callsites_improved = pstats.matrix[27][0] + pstats.matrix[27][1] + pstats.matrix[27][2]
		var total_callsites_improvable = pstats.matrix[26][0] + pstats.matrix[26][1] + pstats.matrix[26][2]

		var total_readsite_improved = pstats.matrix[31][0] + pstats.matrix[31][1] + pstats.matrix[31][2]
		var total_readsite_improvable = pstats.matrix[31][0] + pstats.matrix[31][1] + pstats.matrix[31][2]

		var total_new_improved = pstats.matrix[24][0] + pstats.matrix[24][1] + pstats.matrix[24][2]
		var total_new_improvable = pstats.matrix[23][0] + pstats.matrix[23][1] + pstats.matrix[23][2]

		var total_other_improved = pstats.matrix[29][0] + pstats.matrix[29][1] + pstats.matrix[29][2]
		var total_other_improvable = pstats.matrix[29][0] + pstats.matrix[29][1] + pstats.matrix[29][2] + pstats.matrix[30][0] + pstats.matrix[30][1] + pstats.matrix[30][2]

		var table3 = "CallSite & {if pstats.matrix[26][0] != 0 then pstats.matrix[27][0]*100/pstats.matrix[26][0] else 0} & {if pstats.matrix[26][1] != 0 then pstats.matrix[27][1]*100/pstats.matrix[26][1] else 0} & {if pstats.matrix[26][2] != 0 then pstats.matrix[27][2]*100/pstats.matrix[26][2] else 0}  & {total_callsites_improved*100/total_callsites_improvable}\\\\\n"
		table3 += "ReadSite & {if pstats.matrix[31][0] != 0 then pstats.matrix[31][0]*100/pstats.matrix[31][0] else 0} & {if pstats.matrix[31][1] != 0 then pstats.matrix[31][1]*100/pstats.matrix[31][1] else 0} & {if pstats.matrix[31][2] != 0 then pstats.matrix[31][2]*100/pstats.matrix[31][2] else 0}  & {total_readsite_improved*100/total_readsite_improvable}\\\\\n"
		table3 += "NewSite & {if pstats.matrix[23][0] != 0 then pstats.matrix[24][0]*100/pstats.matrix[23][0] else 0} & {if pstats.matrix[23][1] != 0 then pstats.matrix[24][1]*100/pstats.matrix[23][1] else 0} & {if pstats.matrix[23][2] != 0 then pstats.matrix[24][2]*100/pstats.matrix[23][2] else 0} & {total_new_improved*100/total_new_improvable}\\\\\n"
		table3 += "other & {if pstats.matrix[29][0] != 0 then pstats.matrix[29][0]*100/(pstats.matrix[29][0] + pstats.matrix[30][0]) else 0} & {if pstats.matrix[29][1] != 0 then pstats.matrix[29][1]*100/(pstats.matrix[29][1] + pstats.matrix[30][1]) else 0} & {if pstats.matrix[29][2] != 0 then pstats.matrix[29][2]*100/(pstats.matrix[29][2] + pstats.matrix[30][2]) else 0} & {total_other_improved*100/total_other_improvable}\\\\\n"

		table3 += "\\hline\n"

		var total_improved_method = pstats.matrix[27][0] + pstats.matrix[31][0] + pstats.matrix[24][0] + pstats.matrix[29][0]
		var total_improvable_method = pstats.matrix[26][0] + pstats.matrix[31][0] + pstats.matrix[23][0] + pstats.matrix[29][0] + pstats.matrix[30][0]

		var total_improved_attribute = pstats.matrix[27][1] + pstats.matrix[31][1] + pstats.matrix[24][1] + pstats.matrix[29][1]
		var total_improvable_attribute = pstats.matrix[26][1] + pstats.matrix[31][1] + pstats.matrix[23][1] + pstats.matrix[29][1] + pstats.matrix[30][1]
		if total_improvable_attribute == 0 then total_improvable_attribute = 1

		var total_improved_cast = pstats.matrix[27][2] + pstats.matrix[31][2] + pstats.matrix[24][2] + pstats.matrix[29][2]
		var total_improvable_cast = pstats.matrix[26][2] + pstats.matrix[31][2] + pstats.matrix[23][2] + pstats.matrix[29][2] + pstats.matrix[30][2]
		if total_improvable_cast == 0 then total_improvable_cast = 1

		var total_table3 = (total_improved_method + total_improved_attribute + total_improved_cast)*100/(total_improvable_method + total_improvable_attribute + total_improvable_cast)
		table3 += "total improved & {if total_improvable_method != 0 then total_improved_method*100/total_improvable_method else 0} & {if total_improvable_attribute != 0 then total_improved_attribute*100/total_improvable_attribute else 0} & { if total_improvable_cast != 0 then total_improved_cast*100/total_improvable_cast else 0} & {total_table3}\\\\\n"

		file.write(table3)
		file.write("\n\n")
		file.close
	end

	# Generate a fourth table in latex format
	# `file` An already opened output file
	private fun table4(file: FileWriter)
	do
		file.write("%Table 4\n")

		var optimizable_inline = pstats.matrix[7][0] + pstats.matrix[16][0] + pstats.matrix[10][1] + pstats.matrix[16][1] + pstats.matrix[7][2] + pstats.matrix[10][2] + pstats.matrix[16][2]
		optimizable_inline += pstats.matrix[8][0] + pstats.matrix[17][0] + pstats.matrix[11][1] + pstats.matrix[17][1] + pstats.matrix[8][2] + pstats.matrix[11][2] + pstats.matrix[17][2]

		var nonoptimizable_inline = pstats.matrix[10][0] + pstats.matrix[11][0] + pstats.matrix[12][0] + pstats.matrix[12][1] + pstats.matrix[12][2]
		var total_table4 = optimizable_inline + nonoptimizable_inline

		var total_preexisting = pstats.matrix[7][0] + pstats.matrix[16][0] + pstats.matrix[10][1] + pstats.matrix[16][1] + pstats.matrix[7][2] + pstats.matrix[10][2] + pstats.matrix[16][2]
		var total_nonpreexisting = pstats.matrix[8][0] + pstats.matrix[17][0] + pstats.matrix[11][1] + pstats.matrix[17][1] + pstats.matrix[8][2] + pstats.matrix[11][2] + pstats.matrix[17][2]

		var table4 = "preexisting & {pstats.matrix[7][0] + pstats.matrix[16][0]} & {pstats.matrix[10][1] + pstats.matrix[16][1]} & {pstats.matrix[7][2] + pstats.matrix[10][2] + pstats.matrix[16][2]} & {total_preexisting} & {total_preexisting.to_i*100/total_table4}\\%\\\\\n"
		table4 += "non preexisting & {pstats.matrix[8][0] + pstats.matrix[17][0]} & {pstats.matrix[11][1] + pstats.matrix[17][1]} & {pstats.matrix[8][2] + pstats.matrix[11][2] + pstats.matrix[17][2]} & {total_nonpreexisting} & {total_nonpreexisting.to_i*100/total_table4}\\% \\\\\n"
		table4 += "\\hline\n"

		table4 += "total inlinable & {pstats.matrix[7][0] + pstats.matrix[16][0] + pstats.matrix[8][0] + pstats.matrix[17][0]} & {pstats.matrix[10][1] + pstats.matrix[16][1] + pstats.matrix[11][1] + pstats.matrix[17][1]} & {pstats.matrix[7][2] + pstats.matrix[10][2] + pstats.matrix[16][2] + pstats.matrix[8][2] + pstats.matrix[11][2] + pstats.matrix[17][2]} & {optimizable_inline} & {optimizable_inline*100/total_table4}\\\\\n"
		table4 += "non-inlinable & {pstats.matrix[10][0] + pstats.matrix[11][0] + pstats.matrix[12][0]} & {pstats.matrix[12][1]} & {pstats.matrix[12][2]} & {nonoptimizable_inline} & {nonoptimizable_inline*100/total_table4}\\\\\\hline\n"
		table4 += "total & {pstats.matrix[7][0] + pstats.matrix[16][0] + pstats.matrix[8][0] + pstats.matrix[17][0] + pstats.matrix[10][0] + pstats.matrix[11][0] + pstats.matrix[12][0]} & {pstats.matrix[10][1] + pstats.matrix[16][1] + pstats.matrix[11][1] + pstats.matrix[17][1] + pstats.matrix[12][1]} & {pstats.matrix[7][2] + pstats.matrix[10][2] + pstats.matrix[16][2] + pstats.matrix[8][2] + pstats.matrix[11][2] + pstats.matrix[17][2] + pstats.matrix[12][2]} & {total_table4} & 100\\\\\n"

		file.write(table4)
		file.write("\n\n")
		file.close
	end

	# Statistics of preexsitence by method, pattern and site, for sites with a return (MOCallSite)
	#      | Method | pattern | Site
	# pre  |        |         |
	# npre |        |         |
	# `file` An already opened output file
	private fun table6(file: FileWriter)
	do
		file.write("%Table 6\n")

		var table6 = "preexisting & {pstats.matrix[50][0]} & {pstats.matrix[53][0]} & {pstats.matrix[60][0]}\\\\\n"
		table6 += "non preexisting & {pstats.matrix[51][0]} & {pstats.matrix[54][0] + pstats.matrix[55][0]} & {pstats.matrix[61][0]}\\\\\n"
		table6 += "total & {pstats.matrix[50][0] + pstats.matrix[51][0]} & {pstats.matrix[53][0] + pstats.matrix[54][0] + pstats.matrix[55][0]} & {pstats.matrix[60][0] + pstats.matrix[61][0]}\\\\\n"
		table6 += "\\hline\n"

		table6 += "preexistence rate & {pstats.matrix[50][0]*100/(pstats.matrix[50][0] + pstats.matrix[51][0])} & {pstats.matrix[53][0]*100/(pstats.matrix[53][0] + pstats.matrix[54][0] + pstats.matrix[55][0])} & {pstats.matrix[60][0]*100/(pstats.matrix[60][0] + pstats.matrix[61][0])}\\\\\n"

		table6 += "without return & {pstats.matrix[48][0]} & {pstats.matrix[56][0]} & {pstats.matrix[62][0]}\\\\\n"

		file.write(table6)
		file.write("\n\n")
		file.close
	end
end
