# collect_veri_helpmsg.tcl
# Reads inputs from environment variables:
#   VERI_CODES_FILE : path to file with one VERI-#### per line
#   VERI_OUT_FILE   : output dump file path

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
puts $fout "Generated: [clock format [clock seconds]]"
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

  set tmp ".helpmsg_tmp.txt"
  catch {file delete -force $tmp}

  # Capture helpmsg output
  redirect file $tmp
  set rc [catch {helpmsg $code} emsg]
  redirect off

  if {$rc} {
    puts $fout "ERROR: helpmsg failed for $code"
    puts $fout "DETAIL: $emsg"
    incr n_fail
  } else {
    if {[file exists $tmp]} {
      set t [open $tmp r]
      while {[gets $t l] >= 0} { puts $fout $l }
      close $t
      catch {file delete -force $tmp}
    } else {
      puts $fout "(No output captured for $code)"
    }
    incr n_ok
  }
}

close $fin
puts $fout ""
puts $fout "============================================================"
puts $fout "DONE: ok=$n_ok fail=$n_fail"
close $fout

exit 0
