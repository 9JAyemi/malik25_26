# collect_veri_helpmsg.tcl
# Usage:
#   jg_console -batch -tcl collect_veri_helpmsg.tcl \
#     -codes_file syntax_results/veri_codes.txt \
#     -out_file   syntax_results/veri_helpmsg_dump.txt

proc parse_args {argv} {
  array set o {
    -codes_file ""
    -out_file ""
  }
  for {set i 0} {$i < [llength $argv]} {incr i} {
    set a [lindex $argv $i]
    switch -- $a {
      -codes_file { incr i; set o(-codes_file) [lindex $argv $i] }
      -out_file   { incr i; set o(-out_file)   [lindex $argv $i] }
      default {}
    }
  }
  return [array get o]
}

set opts [parse_args $::argv]
array set o $opts

if {$o(-codes_file) eq "" || $o(-out_file) eq ""} {
  puts "ERROR: need -codes_file and -out_file"
  exit 2
}

if {![file exists $o(-codes_file)]} {
  puts "ERROR: codes_file not found: $o(-codes_file)"
  exit 2
}

set fin [open $o(-codes_file) r]
set fout [open $o(-out_file) w]

puts $fout "Jasper helpmsg dump"
puts $fout "Generated: [clock format [clock seconds]]"
puts $fout "Codes file: $o(-codes_file)"
puts $fout "============================================================"

set n_ok 0
set n_fail 0

while {[gets $fin line] >= 0} {
  set code [string trim $line]
  if {$code eq ""} { continue }

  puts $fout ""
  puts $fout "==== $code ================================================"

  # Some environments print to stdout; we capture by temporarily redirecting
  # to a temp file and then copy it into fout.
  set tmp ".helpmsg_tmp.txt"
  catch {file delete -force $tmp}

  # Redirect stdout to tmp while running helpmsg
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
