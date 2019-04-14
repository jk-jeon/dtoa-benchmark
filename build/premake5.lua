function setTargetObjDir(outDir)
	targetdir(outDir)
	objdir(string.lower("../intermediate/%{cfg.shortname}/" .. _ACTION))
	targetsuffix(string.lower("_%{cfg.shortname}_" .. _ACTION))
end

solution "benchmark"
	configurations { "release" }
	platforms { "x32", "x64" }

	location ("./" .. (_ACTION or ""))
	language "C++"
	flags { warnings "Extra" }
	defines { "__STDC_FORMAT_MACROS=1" }
	
	configuration "release"
		defines { "NDEBUG" }
		flags { optimize "On" }

	configuration "vs*"
		defines { "_CRT_SECURE_NO_WARNINGS" }
		
	configuration "gmake"
		buildoptions "-msse4.2 -O3 -Wall -Wextra -std=c++11"

	project "dtoa"
		kind "ConsoleApp"
		
		files { 
			"../src/**.h",
			"../src/**.c",
			"../src/**.cc",
			"../src/**.cpp",
		}

		setTargetObjDir("../bin")