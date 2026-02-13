# ----------------------------------------
# JasperGold Version Info
# tool      : JasperGold 2021.03
# platform  : Linux 5.14.0-570.84.1.el9_6.x86_64
# version   : 2021.03 FCS 64 bits
# build date: 2021.03.23 02:50:43 UTC
# ----------------------------------------
# started   : 2026-02-13 16:48:11 EST
# hostname  : della9.princeton.edu.(none)
# pid       : 3156080
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:45841' '-nowindow' '-style' 'windows' '-exitonerror' '-data' 'AAAAjnicY2RgYLCp////PwMYMFcBCQEGHwZfhiAGVyDpzxAGpOGA8QGUYcMIUg3EPAy6DEkMiQwlDMkMGUA+B5APYucA2ToMWUCZYoYChlSGIoZ4hjIwncmQBmSDVKcCyWwGPbh6BgCUaBR8' '-proj' '/home/ab2113/malik25_26/metrex/dataset/version_1/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/ab2113/malik25_26/metrex/dataset/version_1/jgproject/.tmp/.initCmds.tcl' 'jasper_verif_check.tcl' '-hidden' '/home/ab2113/malik25_26/metrex/dataset/version_1/jgproject/.tmp/.postCmds.tcl'
# ============================================================
# JasperGold Assertion Verification Runner (env-driven)
# Output: verification_results/<DESIGN_ID>/
#
# Env:
#   DESIGN_ID     : required (subfolder name)
#   JG_TOP        : required top module name
#   JG_DESIGN     : required, space/colon-separated RTL file paths OR a directory
#   JG_SVA        : required, space/colon-separated SVA file paths OR a directory
#
# Optional:
#   JG_STD        : sv12 | sv11 | sv09 (default: sv12)
#   JG_INCDIRS    : colon/space-separated include dirs (optional)
#   JG_DEFINES    : space-separated defines NAME or NAME=VAL (optional)
#   JG_NO_CLOCK   : 1 to force combinational clocking (default: 0)
# ============================================================

proc split_env_list {s} {
  if {$s eq ""} {return {}}
  set out {}
  foreach p [split $s " :"] { if {$p ne ""} {lappend out $p} }
  return $out
}

proc collect_files_any {path} {
  # If path is a file, return it. If directory, glob common HDL extensions.
  if {[file isfile $path]} { return [list $path] }
  if {![file isdirectory $path]} { error "Not a file or directory: $path" }

  set patterns {*.sv *.svh *.v *.vh}
  set flist {}
  foreach p $patterns {
    foreach f [glob -nocomplain -types f -directory $path -tails -- $p] {
      lappend flist [file join $path $f]
    }
  }
  if {[llength $flist] == 0} { error "No HDL files found in directory: $path" }
  return $flist
}

# ---- Read config from environment ----
if {![info exists ::env(DESIGN_ID)] || $::env(DESIGN_ID) eq ""} {
  puts "ERROR: DESIGN_ID not set."
  exit 2
}
if {![info exists ::env(JG_TOP)] || $::env(JG_TOP) eq ""} {
  puts "ERROR: JG_TOP not set."
  exit 2
}
if {![info exists ::env(JG_DESIGN)] || $::env(JG_DESIGN) eq ""} {
  puts "ERROR: JG_DESIGN not set."
  exit 2
}
if {![info exists ::env(JG_SVA)] || $::env(JG_SVA) eq ""} {
  puts "ERROR: JG_SVA not set."
  exit 2
}

set DESIGN_ID $::env(DESIGN_ID)
set TOP       $::env(JG_TOP)
set STD       [expr {[info exists ::env(JG_STD)] ? $::env(JG_STD) : "sv12"}]
set INCDIRS   [expr {[info exists ::env(JG_INCDIRS)] ? [split_env_list $::env(JG_INCDIRS)] : {}}]
set DEFINES   [expr {[info exists ::env(JG_DEFINES)] ? [split_env_list $::env(JG_DEFINES)] : {}}]
set NO_CLOCK  [expr {[info exists ::env(JG_NO_CLOCK)] ? $::env(JG_NO_CLOCK) : 0}]

# JG_DESIGN/JG_SVA can be:
# - a directory
# - a single file
# - a list of files/dirs separated by spaces/colons
set DESIGN_INPUTS [split_env_list $::env(JG_DESIGN)]
set SVA_INPUTS    [split_env_list $::env(JG_SVA)]

set DESIGN_FILES {}
foreach p $DESIGN_INPUTS { set DESIGN_FILES [concat $DESIGN_FILES [collect_files_any $p]] }

set SVA_FILES {}
foreach p $SVA_INPUTS { set SVA_FILES [concat $SVA_FILES [collect_files_any $p]] }

# ---- Output dir ----
set OUT_DIR [file join "verification_results" $DESIGN_ID]
file mkdir $OUT_DIR
set PROP_LIST_TXT [file join $OUT_DIR "property_list.txt"]
set SUMMARY_TXT   [file join $OUT_DIR "summary.txt"]

puts "INFO: Verification run starting"
puts "  DESIGN_ID : $DESIGN_ID"
puts "  TOP       : $TOP"
puts "  STD       : $STD"
puts "  INCDIRS   : $INCDIRS"
puts "  DEFINES   : $DEFINES"
puts "  NO_CLOCK  : $NO_CLOCK"
puts "  N_DESIGN  : [llength $DESIGN_FILES]"
puts "  N_SVA     : [llength $SVA_FILES]"
puts "  OUT_DIR   : $OUT_DIR"

# Optional: promote common message groups to errors (best-effort)
if {[llength [info commands set_msg_config]]} {
  set_msg_config -id COMP*  -severity error
  set_msg_config -id PARSE* -severity error
  set_msg_config -id ELAB*  -severity error
}

# ---- Build analyze options ----
set analyze_opts [list analyze -$STD]
if {[llength $INCDIRS] > 0} { lappend analyze_opts -incdir $INCDIRS }
if {[llength $DEFINES] > 0} {
  foreach d $DEFINES { lappend analyze_opts -define $d }
}

# ---- Analyze + Elaborate ----
set err 0
if {[catch {eval $analyze_opts $DESIGN_FILES} msg]} {
  puts "ERROR: analyze design failed:\n$msg"
  set err 1
}
if {!$err && [catch {eval $analyze_opts $SVA_FILES} msg2]} {
  puts "ERROR: analyze SVA failed:\n$msg2"
  set err 1
}
if {!$err && [catch {elaborate -top $TOP} emsg]} {
  puts "ERROR: elaborate failed:\n$emsg"
  set err 1
}

# If combinational / event-driven, you can force "no clock"
if {!$err && $NO_CLOCK} {
  catch { clock -none }
}

if {$err} {
  puts "\n❌ FAILED: compile/elab errors"
  exit 1
}

# ---- Property discovery (bind sanity check) ----
# Some Jasper builds support: assert -list / cover -list
set ASSERTS {}
set COVERS  {}
catch { set ASSERTS [assert -list -silent] }
catch { set COVERS  [cover  -list -silent] }

puts "INFO: Found [llength $ASSERTS] asserts, [llength $COVERS] covers"

# Write property names (even if empty)
set fp [open $PROP_LIST_TXT "w"]
puts $fp "ASSERT PROPERTIES:"
foreach a $ASSERTS { puts $fp $a }
puts $fp ""
puts $fp "COVER PROPERTIES:"
foreach c $COVERS { puts $fp $c }
close $fp

if {[llength $ASSERTS] == 0 && [llength $COVERS] == 0} {
  puts "\n❌ FAILED: No properties found (bind likely didn't attach, or wrong TOP)"
  exit 3
}

# ---- Prove all assertions ----
# If any assertion FAILS, Jasper will typically set a non-proved status.
# We keep it simple: run prove and rely on Jasper exit status + log parsing later.
puts "INFO: Running prove -all"
if {[catch { prove -all } pmsg]} {
  puts "ERROR: prove command failed:\n$pmsg"
  exit 4
}
