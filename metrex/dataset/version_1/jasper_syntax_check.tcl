# ============================================================
# JasperGold SystemVerilog/SVA Syntax Checker
# ============================================================
# Usage example:
#   jaspergold -batch -tcl jasper_syntax_check.tcl -- -dir ./00000
#   jaspergold -batch -tcl jasper_syntax_check.tcl -- -dir ./00000 -top top_module
#
# Parameters:
#   -dir <directory> : directory containing *.sv/*.v files
#   -std <sv12|sv11|sv09> : SystemVerilog standard (default: sv12)
#   -top <module> : optional, to run elaboration on top module
#   -halt_on_warn : fail run if warnings exist
# ============================================================

proc parse_args {argv} {
  array set opts {
    -dir ""
    -std "sv12"
    -top ""
    -halt_on_warn 0
  }

  for {set i 0} {$i < [llength $argv]} {incr i} {
    set a [lindex $argv $i]
    switch -- $a {
      -dir { incr i; set opts(-dir) [lindex $argv $i] }
      -std { incr i; set opts(-std) [lindex $argv $i] }
      -top { incr i; set opts(-top) [lindex $argv $i] }
      -halt_on_warn { set opts(-halt_on_warn) 1 }
      default { puts "Ignoring unknown arg: $a" }
    }
  }
  return [array get opts]
}

proc collect_files {dir} {
  if {![file isdirectory $dir]} {
    error "Directory not found: $dir"
  }
  set patterns [list *.sv *.svh *.v]
  set flist {}
  foreach p $patterns {
    foreach f [glob -nocomplain -types f -directory $dir -tails -- $p] {
      lappend flist [file join $dir $f]
    }
  }
  if {[llength $flist] == 0} {
    error "No SV/V files found in $dir"
  }
  return $flist
}

set opts [parse_args $::argv]
array set o $opts
set files [collect_files $o(-dir)]

file mkdir .jasper_logs
set logf ".jasper_logs/syntax_check.log"
set jsonf ".jasper_logs/syntax_check.json"
redirect file $logf

set err 0

puts "INFO: Analyzing directory $o(-dir)"
set cmd [list analyze -$o(-std)]
foreach f $files { lappend cmd $f }

if {[catch {eval $cmd} msg]} {
  puts "ERROR: Analyze failed:\n$msg"
  set err 1
} else {
  puts "INFO: Analyze completed."
}

# Optional: elaborate if top provided
if {!$err && [string length $o(-top)]} {
  puts "INFO: Elaborating top $o(-top)"
  if {[catch {elaborate $o(-top)} emsg]} {
    puts "ERROR: Elaborate failed:\n$emsg"
    set err 1
  } else {
    puts "INFO: Elaborate completed."
  }
}

redirect off

# Check for failures
set warn_count 0
catch {set warn_count [get_warning_count]}

if {$err} {
  puts "\n❌ FAILED: Syntax/elaboration errors detected"
  exit 1
}

if {$o(-halt_on_warn) && $warn_count > 0} {
  puts "\n⚠️  FAILED: $warn_count warnings detected (halt_on_warn enabled)"
  exit 1
}

puts "\n✅ PASSED: Syntax check successful"
exit 0
