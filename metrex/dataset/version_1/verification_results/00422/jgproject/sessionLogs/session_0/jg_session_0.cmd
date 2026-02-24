# ----------------------------------------
# JasperGold Version Info
# tool      : JasperGold 2021.03
# platform  : Linux 5.14.0-570.84.1.el9_6.x86_64
# version   : 2021.03 FCS 64 bits
# build date: 2021.03.23 02:50:43 UTC
# ----------------------------------------
# started   : 2026-02-23 13:38:16 EST
# hostname  : della-i13n20.(none)
# pid       : 1133282
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:44973' '-nowindow' '-style' 'windows' '-exitonerror' '-data' 'AAAA8HicTY69CsJAEIS/QwQRC19EE8QyrV1EsLA9NJyaGFS8aGHjq/om5+TQ4C67tz8zs2eA7BVCIFrvqTQmZ8mahfKKjd7OzPtbZEaprxgxYceWhoKj+qH6KzcuVOpypiQ8cJqU7BVFxJban7GaOjx3as28kKl8zkyeiH/olJx4jfQGUm8v1arTqF1JzwvXXrB/l2z8T8s7Cffj8AGjWSUM' '-proj' '/home/ab2113/malik25_26/metrex/dataset/version_1/verification_results/00422/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/ab2113/malik25_26/metrex/dataset/version_1/verification_results/00422/jgproject/.tmp/.initCmds.tcl' './jasper_verif_check.tcl' '-hidden' '/home/ab2113/malik25_26/metrex/dataset/version_1/verification_results/00422/jgproject/.tmp/.postCmds.tcl'
# ============================================================
# JasperGold Assertion Verification Runner (env-driven)
# Output: verification_results/<DESIGN_ID>/
#
# Env:
#   DESIGN_ID     : required (subfolder name)
#   JG_DESIGN     : required, space/colon-separated RTL file paths OR a directory
#   JG_SVA        : required, space/colon-separated SVA file paths OR a directory
#
# Optional:
#   JG_TOP        : top module name. If missing, inferred from RTL (default: infer)
#   JG_STD        : sv12 | sv11 | sv09 (default: sv12)
#   JG_INCDIRS    : colon/space-separated include dirs (optional)
#   JG_DEFINES    : space-separated defines NAME or NAME=VAL (optional)
#   JG_NO_CLOCK   : 1 to force combinational clocking (default: 0)
#   JG_RESET      : explicit reset signal name (optional)
#   JG_RESET_EXPR : explicit reset expression (optional)
# ============================================================

proc split_env_list {s} {
  if {$s eq ""} {return {}}
  set out {}
  foreach p [split $s " :"] { if {$p ne ""} {lappend out $p} }
  return $out
}

proc split_space_list {s} {
  if {$s eq ""} {return {}}
  set out {}
  foreach p [split $s " "] { if {$p ne ""} {lappend out $p} }
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

proc read_file_text {path} {
  set fp [open $path "r"]
  set data [read $fp]
  close $fp
  return $data
}

proc strip_comments {text} {
  set out $text
  regsub -all {(?s)/\*.*?\*/} $out "" out
  regsub -all {(?m)//.*$} $out "" out
  return $out
}

proc infer_top_from_file {f} {
  if {![file isfile $f]} { return "" }
  set txt [strip_comments [read_file_text $f]]
  if {[regexp -nocase -line {^\s*module\s+([A-Za-z_][A-Za-z0-9_]*)} $txt -> m]} {
    return $m
  }
  return ""
}

proc find_reset_signal {top files} {
  set top_l [string tolower $top]
  set keywords {input output inout wire reg logic signed unsigned integer parameter localparam bit tri supply0 supply1 tri0 tri1 wand wor}
  foreach f $files {
    if {![file isfile $f]} { continue }
    set txt [strip_comments [read_file_text $f]]
    set re "(?s)\\mmodule\\s+${top_l}\\M\\s*(#\\s*\\(.*?\\)\\s*)?\\((.*?)\\)\\s*;"
    if {[regexp -nocase -- $re $txt -> _port_params portlist]} {
      set tokens [regexp -all -inline {\m[A-Za-z_][A-Za-z0-9_]*\M} $portlist]
      set names {}
      foreach t $tokens {
        set tl [string tolower $t]
        if {[lsearch -exact $keywords $tl] >= 0} { continue }
        lappend names $t
      }
      if {[llength $names] == 0} { continue }
      set lower_map [dict create]
      foreach n $names { dict set lower_map [string tolower $n] $n }
      set exact_priority {reset_n rst_n resetb rstb resetn rstn areset_n arst_n reset rst areset arst}
      foreach p $exact_priority {
        if {[dict exists $lower_map $p]} { return [dict get $lower_map $p] }
      }
      foreach n $names {
        set ln [string tolower $n]
        if {[regexp {(^|_)reset(_|$)} $ln] || [regexp {(^|_)rst(_|$)} $ln]} {
          return $n
        }
      }
    }
  }
  return ""
}

# ---- Read config from environment ----
if {![info exists ::env(DESIGN_ID)] || $::env(DESIGN_ID) eq ""} {
  puts "ERROR: DESIGN_ID not set."
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

# JG_TOP is optional: if missing, infer from RTL
set TOP ""
if {[info exists ::env(JG_TOP)] && $::env(JG_TOP) ne ""} {
  set TOP $::env(JG_TOP)
}

set STD      [expr {[info exists ::env(JG_STD)] ? $::env(JG_STD) : "sv12"}]
set INCDIRS  [expr {[info exists ::env(JG_INCDIRS)] ? [split_env_list $::env(JG_INCDIRS)] : {}}]
# Defines should be space-separated (do NOT split on ':')
set DEFINES  [expr {[info exists ::env(JG_DEFINES)] ? [split_space_list $::env(JG_DEFINES)] : {}}]
set NO_CLOCK [expr {[info exists ::env(JG_NO_CLOCK)] ? $::env(JG_NO_CLOCK) : 0}]

# JG_DESIGN/JG_SVA can be:
# - a directory
# - a single file
# - a list of files/dirs separated by spaces/colons
set DESIGN_INPUTS [split_env_list $::env(JG_DESIGN)]
set SVA_INPUTS    [split_env_list $::env(JG_SVA)]

set DESIGN_FILES {}
foreach p $DESIGN_INPUTS { set DESIGN_FILES [concat $DESIGN_FILES [collect_files_any $p]] }

# Infer TOP if not provided
if {$TOP eq ""} {
  foreach f $DESIGN_FILES {
    set guess [infer_top_from_file $f]
    if {$guess ne ""} { set TOP $guess; break }
  }
  if {$TOP eq ""} {
    puts "ERROR: Could not infer TOP from design files; set JG_TOP explicitly."
    exit 2
  }
}
puts "INFO: Using TOP = $TOP"

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
puts "DEBUG: DESIGN_FILES = $DESIGN_FILES"
puts "DEBUG: SVA_FILES    = $SVA_FILES"

if {[catch {eval $analyze_opts $DESIGN_FILES} msg]} {
  puts "ERROR: analyze design failed:\n$msg"
  set err 1
}
if {!$err && [catch {eval $analyze_opts $SVA_FILES} msg2]} {
  puts "ERROR: analyze SVA failed:\n$msg2"
  set err 1
}

puts "DEBUG: Elaborating TOP='$TOP'"
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

# ---- Reset -----
set RESET_SIG ""
set RESET_EXPR ""
if {[info exists ::env(JG_RESET_EXPR)] && $::env(JG_RESET_EXPR) ne ""} {
  set RESET_EXPR $::env(JG_RESET_EXPR)
} elseif {[info exists ::env(JG_RESET)] && $::env(JG_RESET) ne ""} {
  set RESET_SIG $::env(JG_RESET)
} else {
  set RESET_SIG [find_reset_signal $TOP $DESIGN_FILES]
}

if {$RESET_EXPR ne ""} {
  puts "INFO: Using reset expression: $RESET_EXPR"
  catch { reset -expression $RESET_EXPR }
} elseif {$RESET_SIG ne ""} {
  if {[regexp -nocase {(_n|_b)$} $RESET_SIG]} {
    set RESET_EXPR "!$RESET_SIG"
    puts "INFO: Using active-low reset expression: $RESET_EXPR"
    catch { reset -expression $RESET_EXPR }
  } else {
    puts "INFO: Using reset signal: $RESET_SIG"
    catch { reset $RESET_SIG }
  }
} else {
  puts "INFO: No reset signal found; using reset -none"
  catch { reset -none }
}

# ---- Property discovery (bind sanity check) ----
set ASSERTS {}
set COVERS  {}
catch { set ASSERTS [assert -list -silent] }
catch { set COVERS  [cover  -list -silent] }

puts "INFO: Found [llength $ASSERTS] asserts, [llength $COVERS] covers"

# Write property names
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
# 3600 seconds = 1 hour timeout per property (adjust as needed)
set_prove_time_limit 3600
puts "INFO: Running prove -all"
if {[catch { prove -all } pmsg]} {
  puts "ERROR: prove command failed:\n$pmsg"
  exit 4
}

# ---- Covers (best effort) ----
catch { cover -all }

# ---- Write summary ----
set fp [open $SUMMARY_TXT "w"]
puts $fp "DESIGN_ID=$DESIGN_ID"
puts $fp "TOP=$TOP"
puts $fp "ASSERT_COUNT=[llength $ASSERTS]"
puts $fp "COVER_COUNT=[llength $COVERS]"
puts $fp "PROP_LIST=$PROP_LIST_TXT"
close $fp

puts "\n✅ DONE: Proof run completed (check Jasper property table / log for PROVED/FAILED)"
puts "INFO: Wrote $SUMMARY_TXT"
puts "INFO: Wrote $PROP_LIST_TXT"
exit 0
