# collect_veri_helpmsg.tcl
# Reads inputs from environment variables:
#   VERI_CODES_FILE : path to file with one VERI-#### per line
#   VERI_OUT_FILE   : output dump file path

# Load a minimal design to avoid "No design modules" error
if {[catch {analyze -verilog empty.v} err]} {
  puts "Warning: Could not analyze empty.v: $err"
}
if {[catch {elaborate -top empty_design} err]} {
  puts "Warning: Could not elaborate: $err"
}

proc getenv_or_die {name} {
  if {![info exists ::env($name)] || [string trim $::env($name)] eq ""} {
    puts "ERROR: environment variable $name is not set"
    exit 2
  }
  return [string trim $::env($name)]
}

set codes_file [getenv_or_die "VERI_CODES_FILE"]
set out_file   [getenv_or_die "VERI_OUT_FILE"]

if {![file exists $codes_file]} {
  puts "ERROR: codes_file not found: $codes_file"
  exit 2
}

set fin  [open $codes_file r]
set fout [open $out_file w]

puts $fout "Jasper helpmsg dump"
puts $fout "Codes file: $codes_file"
puts $fout "============================================================"

set n_ok 0
set n_fail 0

while {[gets $fin line] >= 0} {
  set code [string trim $line]
  if {$code eq ""} { continue }

  puts "DEBUG: Processing $code"
  flush stdout

  puts $fout ""
  puts $fout "==== $code ================================================"

  # Get helpmsg output directly
  set rc [catch {helpmsg $code} result]

  if {$rc} {
    puts $fout "ERROR: helpmsg failed for $code"
    puts $fout "DETAIL: $result"
    incr n_fail
  } else {
    puts $fout "$result"
    incr n_ok
  }
}

close $fin
puts $fout ""
puts $fout "============================================================"
puts $fout "DONE: ok=$n_ok fail=$n_fail"
close $fout

exit 0
