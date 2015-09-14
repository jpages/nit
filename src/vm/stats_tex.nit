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

		# Line "other", the difference between npre from first table for each category minus the column from
		var other_methods = pstats.matrix[2][0] - (pstats.matrix[23][0] + pstats.matrix[26][0] + pstats.matrix[31][0])
		var other_attributes = pstats.matrix[2][1] - (pstats.matrix[23][1] + pstats.matrix[26][1] + pstats.matrix[31][1])
		var other_casts = pstats.matrix[2][2] - (pstats.matrix[23][2] + pstats.matrix[26][2] + pstats.matrix[31][2])
		var total_others = other_methods + other_attributes + other_casts

		var total_from_new = pstats.matrix[23][0] + pstats.matrix[23][1] + pstats.matrix[23][2]
		var total_from_callsite = pstats.matrix[26][0] + pstats.matrix[26][1] + pstats.matrix[26][2]
		var total_from_readsite = pstats.matrix[31][0] + pstats.matrix[31][1] + pstats.matrix[31][2]

		var general_total = total_from_new + total_from_callsite + total_from_readsite + other_methods + other_attributes + other_casts

		var table2 = "ReadSite & {pstats.matrix[31][0]} & {pstats.matrix[31][1]} & {pstats.matrix[31][2]} & {total_from_readsite} & {total_from_readsite*100/general_total}\\\\\n"
		table2 += "NewSite & {pstats.matrix[23][0]} & {pstats.matrix[23][1]} & {pstats.matrix[23][2]} & {total_from_new} & {total_from_new*100/general_total}\\\\\n"
		table2 += "CallSite & {pstats.matrix[26][0]} & {pstats.matrix[26][1]} & {pstats.matrix[26][2]} & {total_from_callsite} & {total_from_callsite*100/general_total}\\\\\n"
		table2 += "other & {other_methods} & {other_attributes} & {other_casts} & {total_others} & {total_others*100/general_total}\\\\\n"
		table2 += "\\hline\n"

		improvable_methods = pstats.matrix[26][0] + other_methods
		improvable_attributes = pstats.matrix[26][1] + other_attributes
		improvable_casts = pstats.matrix[26][2] + other_casts
		total_improvable = improvable_methods + improvable_attributes + improvable_casts

		table2 += "%improvable total & {improvable_methods} & {improvable_attributes} & {improvable_casts} & {total_improvable} & {total_improvable*100/general_total}\\\\\n"

		table2 += "total & {pstats.matrix[23][0] + pstats.matrix[26][0] + pstats.matrix[31][0] + other_methods} & {pstats.matrix[23][1] + pstats.matrix[26][1] + pstats.matrix[31][1] + other_attributes} & {pstats.matrix[23][2] + pstats.matrix[26][2] + pstats.matrix[31][2] + other_casts} & {general_total} & 100\\\\\n"

		file.write(table2)
		file.write("\n\n")
		file.close
	end

	# Generate a third table in latex format
	# `file` An already opened output file
	private fun table3(file: FileWriter)
	do
		file.write("%Table 3\n")

		var total_other = pstats.matrix[56][0] + pstats.matrix[56][1] + pstats.matrix[56][2]
		var total_callsites = pstats.matrix[28][0] + pstats.matrix[28][1] + pstats.matrix[28][2]
		var total_table3 = total_other + total_callsites

		# Get improvable_methods from table2-original
		var reader = new FileReader.open("output_latex/table2-last-original.tex")
		var lines = reader.read_lines
		var improvables = lines[6].split('&')
		reader.close

		var table3 = "CallSite & {pstats.matrix[28][0]} & {pstats.matrix[28][1]} & {pstats.matrix[28][2]} & {total_callsites} & {total_callsites*100/improvables[4].to_i}\\\\\n"
		table3 += "other & {pstats.matrix[56][0]} & {pstats.matrix[56][1]} & {pstats.matrix[56][2]} & {total_other} & {total_other*100/improvables[4].to_i}\\\\\n"

		table3 += "\\hline\n"
		table3 += "total improved & {pstats.matrix[23][0] + pstats.matrix[28][0]} & {pstats.matrix[23][1] + pstats.matrix[28][1]} & {pstats.matrix[23][2] + pstats.matrix[28][2]} & {total_table3} & {total_table3*100/improvables[4].to_i}\\\\\n"
		table3 += "improvable total & {improvables[1]} & {improvables[2]} & {improvables[3]} & {improvables[4]} & 100\\\\\n"

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

	# Statistics of preexsitence by method, pattern and site, for sites with a return
	#      | Method | pattern | Site
	# pre  |        |         |
	# npre |        |         |
	# `file` An already opened output file
	private fun table6(file: FileWriter)
	do
		file.write("%Table 6\n")

		var table6 = "preexisting & {pstats.matrix[50][0]} & {pstats.matrix[53][0]} & {pstats.matrix[1][5]}\\\\\n"
		table6 += "non preexisting & {pstats.matrix[51][0]} & {pstats.matrix[54][0]} & {pstats.matrix[2][5]}\\\\\n"
		table6 += "total & {pstats.matrix[50][0] + pstats.matrix[51][0]} & {pstats.matrix[53][0] + pstats.matrix[54][0]} & {pstats.matrix[1][5] + pstats.matrix[2][5]}\\\\\n"
		table6 += "\\hline\n"

		table6 += "preexistence rate & {pstats.matrix[49][0]*100/(pstats.matrix[50][0] + pstats.matrix[51][0])} & {pstats.matrix[53][0]*100/(pstats.matrix[53][0] + pstats.matrix[54][0])} & {pstats.matrix[1][5]*100/(pstats.matrix[1][5] + pstats.matrix[2][5])}\\\\\n"

		table6 += "without return & {pstats.matrix[48][0]} & {pstats.matrix[55][0]} & {}\\\\\n"

		file.write(table6)
		file.write("\n\n")
		file.close
	end
end
