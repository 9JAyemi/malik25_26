# ----------------------------------------
# JasperGold Version Info
# tool      : JasperGold 2021.03
# platform  : Linux 5.14.0-570.62.1.el9_6.x86_64
# version   : 2021.03 FCS 64 bits
# build date: 2021.03.23 02:50:43 UTC
# ----------------------------------------
# started   : 2025-11-15 20:04:58 EST
# hostname  : della9.princeton.edu.(none)
# pid       : 2027880
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:43329' '-nowindow' '-style' 'windows' '-exitonerror' '-data' 'AAAAlHicY2RgYLCp////PwMYMFcBCQEGHwZfhiAGVyDpzxAGpOGA8QGUYcMIUg3EPAy6DEkMiQwlDMkMGUA+B5APYucA2UYMegz6DFlA2WKGAoZUhiKGeCCrkiEPqCKRoQLIA+lJBZLZQJUwXQwABtcVag==' '-proj' '/home/ab2113/malik25_26/metrex/dataset/version_1/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/ab2113/malik25_26/metrex/dataset/version_1/jgproject/.tmp/.initCmds.tcl' './jasper_syntax_check.tcl' '-hidden' '/home/ab2113/malik25_26/metrex/dataset/version_1/jgproject/.tmp/.postCmds.tcl'
# ============================================================
# JasperGold SystemVerilog/SVA Syntax Checker (env-driven)
# No Tcl redirect; rely on shell redirection for logs.
# Env:
#   JG_DIR          : dir with *.sv/*.svh/*.v (required)
#   JG_STD          : sv12 | sv11 | sv09 (default: sv12)
#   JG_TOP          : optional top to elaborate
#   JG_HALT_ON_WARN : 1 to fail if warnings exist (default: 0)
#   JG_INCDIRS      : colon/space-separated include dirs (optional)
#   JG_DEFINES      : space-separated defines NAME or NAME=VAL (optional)
# ============================================================

proc split_env_list {s} {
  if {$s eq ""} {return {}}
  set out {}
  foreach p [split $s " :"] { if {$p ne ""} {lappend out $p} }
  return $out
}

# ---- Read config from environment ----
if {![info exists ::env(JG_DIR)] || $::env(JG_DIR) eq ""} {
  puts "ERROR: JG_DIR not set. Export JG_DIR to the RTL directory."
  exit 2
}
set DIR          $::env(JG_DIR)
set STD          [expr {[info exists ::env(JG_STD)] ? $::env(JG_STD) : "sv12"}]
set TOP          [expr {[info exists ::env(JG_TOP)] ? $::env(JG_TOP) : ""}]
set HALT_ON_WARN [expr {[info exists ::env(JG_HALT_ON_WARN)] ? $::env(JG_HALT_ON_WARN) : 0}]
set INCDIRS      [expr {[info exists ::env(JG_INCDIRS)] ? [split_env_list $::env(JG_INCDIRS)] : {}}]
set DEFINES_KV   [expr {[info exists ::env(JG_DEFINES)] ? [split_env_list $::env(JG_DEFINES)] : {}}]

# ---- Collect files in JG_DIR ----
proc collect_files {dir} {
  if {![file isdirectory $dir]} { error "Directory not found: $dir" }
  set patterns {*.sv *.svh *.v}
  set flist {}
  foreach p $patterns {
    foreach f [glob -nocomplain -types f -directory $dir -tails -- $p] {
      lappend flist [file join $dir $f]
    }
  }
  if {[llength $flist] == 0} { error "No SV/V files found in $dir" }
  return $flist
}
set FILES [collect_files $DIR]

puts "INFO: Syntax check starting"
puts "  DIR      : $DIR"
puts "  STD      : $STD"
puts "  TOP      : [expr {$TOP eq "" ? "(none)" : $TOP}]"
puts "  INCDIRS  : $INCDIRS"
puts "  DEFINES  : $DEFINES_KV"
puts "  NFILES   : [llength $FILES]"

# Promote common message groups to errors if available
if {[llength [info commands set_msg_config]]} {
  set_msg_config -id COMP*  -severity error
  set_msg_config -id PARSE* -severity error
  set_msg_config -id ELAB*  -severity error
}

# ---- Build analyze options ----
set analyze_opts [list analyze -$STD]
if {[llength $INCDIRS] > 0} {
  lappend analyze_opts -incdir $INCDIRS
}
if {[llength $DEFINES_KV] > 0} {
  foreach d $DEFINES_KV { lappend analyze_opts -define $d }
}

# ---- Analyze ----
set err 0
if {[catch {eval $analyze_opts $FILES} msg]} {
  puts "ERROR: analyze failed:\n$msg"
  set err 1
} else {
  puts "INFO: analyze completed."
}

# ---- Elaborate (optional) ----
if {!$err && $TOP ne ""} {
  puts "INFO: elaborate $TOP"
  if {[catch {elaborate $TOP} emsg]} {
    puts "ERROR: elaborate failed:\n$emsg"
    set err 1
  } else {
    puts "INFO: elaborate completed."
  }
}

# ---- Warning count (best-effort) ----
set warn_count 0
if {[llength [info commands get_messages]]} {
  set warns [get_messages -severity WARNING]
  set warn_count [llength $warns]
}

if {$err} {
  puts "\n❌ FAILED: Syntax/elaboration errors detected"
  exit 1
}
