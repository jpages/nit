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

import stats

# Output the statistics to .tex files
module stats_tex

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
		var file = new FileWriter.open("tables-{lbl}.tex")

		file.write("%Table 1\n")

		# Table 1: Original preexistence
		var table1 = "\\hline\n"

		var total_pre = (pstats.matrix[1][0] + pstats.matrix[1][1] + pstats.matrix[1][2]).to_f
		var total_npre = (pstats.matrix[2][0] + pstats.matrix[2][1] + pstats.matrix[2][2]).to_f
		#TODO: compatibiliser les asnotnull avec les casts ?
		table1 += "preexisting & {pstats.matrix[1][0]} & {pstats.matrix[1][1]} & {pstats.matrix[1][2]} & {total_pre} & {(total_pre*100.0/(total_pre+total_npre)).to_f}\\%\\\\\n"
		table1 += "non preexisting & {pstats.matrix[2][0]} & {pstats.matrix[2][1]} & {pstats.matrix[2][2]} & \\textbf\{{total_npre}\} & \\textbf\{{(total_npre*100.0/(total_pre+total_npre)).to_f}\\%\}\\\\\n"
		table1 += "\\hline\n"
		table1 += "total & {pstats.matrix[1][0] + pstats.matrix[2][0]} & {pstats.matrix[1][1] + pstats.matrix[2][1]} & {pstats.matrix[1][2] + pstats.matrix[2][2]} & {total_pre + total_npre}\n"

		file.write(table1)
		file.write("\n\n")

		file.write("%Table 2\n")
		var table2 = "\\hline\n"

		# Totals for each categories
		var total_methods = pstats.matrix[1][0] + pstats.matrix[2][0]
		var total_attributes = pstats.matrix[1][1] + pstats.matrix[2][1]
		var total_casts = pstats.matrix[1][2] + pstats.matrix[2][2]

		# Line "other", the difference between pre+npre for each category minus the column from
		var other_methods = total_methods - (pstats.matrix[23][0] + pstats.matrix[26][0] + pstats.matrix[31][0])
		var other_attributes = total_attributes - (pstats.matrix[23][1] + pstats.matrix[26][1] + pstats.matrix[31][1])
		var other_casts = total_casts - (pstats.matrix[23][2] + pstats.matrix[26][2] + pstats.matrix[31][2])
		var total_others = other_methods + other_attributes + other_casts

		var total_from_new = pstats.matrix[23][0] + pstats.matrix[23][1] + pstats.matrix[23][2]
		var total_from_callsite = pstats.matrix[26][0] + pstats.matrix[26][1] + pstats.matrix[26][2]
		var total_from_readsite = pstats.matrix[31][0] + pstats.matrix[31][1] + pstats.matrix[31][2]

		var general_total = total_from_new + total_from_callsite + total_from_readsite + other_methods + other_attributes + other_casts

		table2 += "NewSite & {pstats.matrix[23][0]} & {pstats.matrix[23][1]} & {pstats.matrix[23][2]} & {total_from_new} & {total_from_new*100/general_total}\\% \\\\\n"
		table2 += "CallSite & {pstats.matrix[26][0]} & {pstats.matrix[26][1]} & {pstats.matrix[26][2]} & {total_from_callsite} & {total_from_callsite*100/general_total}\\%\\\\\n"
		table2 += "ReadSite & {pstats.matrix[31][0]} & {pstats.matrix[31][1]} & {pstats.matrix[31][2]} & {total_from_readsite} & {total_from_readsite*100/general_total}\\%\\\\\n"
		table2 += "other & {other_methods} & {other_attributes} & {other_casts} & {total_others} & {total_others*100/general_total}\\%\\\\\n"
		table2 += "\\hline\n"

		var improvable_methods = pstats.matrix[23][0] + pstats.matrix[26][0] + other_methods
		var improvable_attributes = pstats.matrix[23][1] + pstats.matrix[26][1] + other_attributes
		var improvable_casts = pstats.matrix[23][2] + pstats.matrix[26][2] + other_casts
		var total_improvable = improvable_methods + improvable_attributes + improvable_casts

		table2 += "improvable total & {improvable_methods} & {improvable_attributes} & {improvable_casts} & {total_improvable} & 100 \\% \\\\\n"
		table2 += "total & {pstats.matrix[23][0] + pstats.matrix[26][0] + pstats.matrix[31][0] + other_methods} & {pstats.matrix[23][1] + pstats.matrix[26][1] + pstats.matrix[31][1] + other_attributes} & {pstats.matrix[23][2] + pstats.matrix[26][2] + pstats.matrix[31][2] + other_casts} & {general_total} & 100\\%\n"

		file.write(table2)
		file.write("\n\n")

		file.write("%Table 3\n")
		var table3 = "\\hline\n"

		var total_newsites = pstats.matrix[23][0] + pstats.matrix[23][1] + pstats.matrix[23][2]
		var total_callsites = pstats.matrix[28][0] + pstats.matrix[28][1] + pstats.matrix[28][2]
		var total_table3 = total_newsites + total_callsites

		table3 += "NewSite & {pstats.matrix[23][0]} & {pstats.matrix[23][1]} & {pstats.matrix[23][2]} & {total_newsites} & 37\\% \\\\\n"
		table3 += "CallSite & {pstats.matrix[28][0]} & {pstats.matrix[28][1]} & {pstats.matrix[28][2]} & {total_callsites} & 0\\% \\\\\n"

		table3 += "\\hline\n"
		table3 += "improvable total & {improvable_methods} & {improvable_attributes} & {improvable_casts} & {total_improvable} & 100 \\% \\\\\n"
		table3 += "total & {pstats.matrix[23][0] + pstats.matrix[28][0]} & {pstats.matrix[23][1] + pstats.matrix[28][1]} & {pstats.matrix[23][2] + pstats.matrix[28][2]} & {total_table3} & 59\\%\n"

		file.write(table3)
		file.write("\n\n")

		file.write("%Table 4\n")

		var total_inlinable = pstats.matrix[6][0] + pstats.matrix[15][0] + pstats.matrix[6][1] + pstats.matrix[15][1] + pstats.matrix[6][2] + pstats.matrix[15][2]
		var total_noninlinable = pstats.matrix[9][0] + pstats.matrix[12][0] + pstats.matrix[9][1] + pstats.matrix[12][1] + pstats.matrix[9][2] + pstats.matrix[12][2]
		var total_table4 = total_inlinable + total_noninlinable

		var table4 = "preexisting & {pstats.matrix[1][0]} & {pstats.matrix[1][1]} & {pstats.matrix[1][2]} & {total_pre.to_i} & {total_pre.to_i*100/total_table4}\\%\\\\\n"
		table4 += "non preexisting & {pstats.matrix[2][0]} & {pstats.matrix[2][1]} & {pstats.matrix[2][2]} & {total_npre.to_i} & {total_npre.to_i*100/total_table4}\\% \\\\\n"
		table4 += "\\hline\n"

		table4 += "total inlinable & {pstats.matrix[6][0] + pstats.matrix[15][0]} & {pstats.matrix[6][1] + pstats.matrix[15][1]} &	{pstats.matrix[6][2] + pstats.matrix[15][2]} & {total_inlinable} & {total_inlinable*100/total_table4}\\%\\\\\n"
		table4 += "non inlinable & {pstats.matrix[9][0] + pstats.matrix[12][0]} & {pstats.matrix[9][1] + pstats.matrix[12][1]} & {pstats.matrix[9][2] + pstats.matrix[12][2]} & {total_noninlinable} & {total_noninlinable*100/total_table4}\\%\\\\\\hline\n"
		table4 += "total & {pstats.matrix[6][0] + pstats.matrix[15][0] + pstats.matrix[9][0] + pstats.matrix[12][0]} & {pstats.matrix[6][1] + pstats.matrix[15][1] + pstats.matrix[9][1] + pstats.matrix[12][1]} & {pstats.matrix[6][2] + pstats.matrix[15][2] + pstats.matrix[9][2] + pstats.matrix[12][2]} & {total_table4} & 100\\%\n"

		file.write(table4)
		file.write("\n\n")
		file.close
	end