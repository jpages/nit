#!/usr/bin/env nit
#
# This file is part of NIT ( http://www.nitlanguage.org ).
# This program is public domain

# Task: Box The Compass
# SEE: <http://rosettacode.org/wiki/Box_the_compass>

var names = ["North", "North by east", "North-northeast", "Northeast by north", "Northeast","Northeast by east",
	    "East-northeast", "East by north", "East", "East by south", "East-southeast", "Southeast by east", "Southeast",
            "Southeast by south", "South-southeast", "South by east", "South", "South by west", "South-southwest", "Southwest by south",
            "Southwest", "Southwest by west", "West-southwest", "West by south", "West", "West by north", "West-northwest",
            "Northwest by west", "Northwest", "Northwest by north", "North-northwest", "North by west", "North"]

var degrees = [0.0, 16.87, 16.88, 33.75, 50.62, 50.63, 67.5,
                84.37, 84.38, 101.25, 118.12, 118.13, 135.0, 151.87, 151.88,
                168.75, 185.62, 185.63, 202.5, 219.37, 219.38, 236.25, 253.12,
                253.13, 270.0, 286.87, 286.88, 303.75, 320.62, 320.63, 337.5,
                354.37, 354.38]

for d in degrees do
	var h = (d / 11.25 + 0.5).floor.to_i % 32
	print "{h+1} {names[h]} {d}"
end
