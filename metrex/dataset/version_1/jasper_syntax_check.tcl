# ============================================================
# JasperGold SystemVerilog/SVA Syntax Checker (env-driven)
# Compatible with Jasper 2021.x and later
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

# ---- Collect files ----
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

# ---- Logging ----
file mkdir .jasper_logs
set LOGF ".jasper_logs/syntax_check.log"
redirect start file $LOGF

puts "INFO: Syntax check starting"
puts "  DIR      : $DIR"
puts "  STD      : $STD"
puts "  TOP      : [expr {$TOP eq \"\" ? \"(none)\" : $TOP}]"
puts "  INCDIRS  : $INCDIRS"
puts "  DEFINES  : $DEFINES_KV"
puts "  NFILES   : [llength $FILES]"

# ---- Make parsing/elab errors fatal ----
if {[llength [info commands set_msg_config]]} {
  set_msg_config -id COMP*  -severity error
  set_msg_config -id PARSE* -severity error
  set_msg_config -id ELAB*  -severity error
}

# ---- Build analyze command ----
set analyze_opts [list analyze -$STD]
if {[llength $INCDIRS] > 0} { lappend analyze_opts -incdir $INCDIRS }
if {[llength $DEFINES_KV] > 0} {
  foreach d $DEFINES_KV { lappend analyze_opts -define $d }
}

# ---- Run analyze ----
set err 0
if {[catch {eval $analyze_opts $FILES} msg]} {
  puts "ERROR: analyze failed:\n$msg"
  set err 1
} else {
  puts "INFO: analyze completed."
}

# ---- Optional elaborate ----
if {!$err && $TOP ne ""} {
  puts "INFO: elaborate $TOP"
  if {[catch {elaborate $TOP} emsg]} {
    puts "ERROR: elaborate failed:\n$emsg"
    set err 1
  } else {
    puts "INFO: elaborate completed."
  }
}

redirect stop

# ---- Count warnings ----
set warn_count 0
if {[llength [info commands get_messages]]} {
  set warns [get_messages -severity WARNING]
  set warn_count [llength $warns]
}

if {$err} {
  puts "\n❌ FAILED: Syntax/elaboration errors detected (see $LOGF)"
  exit 1
}
if {$HALT_ON_WARN && $warn_count > 0} {
  puts "\n⚠️  FAILED: $warn_count warnings detected (HALT_ON_WARN=1) — see $LOGF"
  exit 1
}

puts "\n✅ PASSED: Syntax check successful"
exit 0
