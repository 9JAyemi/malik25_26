// SVA for mux_2to1
// Checks delta-cycle pipelining and mux functionality with full but concise coverage.

module mux_2to1_sva;
  // Bind module has no ports; signals are referenced in bound instance scope.
  // Sampling on any input transition; use ##0 steps to walk delta-cycle pipeline.
  default clocking cb @(posedge ctrl or negedge ctrl
                       or posedge data[0] or negedge data[0]
                       or posedge data[1] or negedge data[1]); endclocking

  // Sanity: no X/Z on inputs when they change
  ap_inputs_known: assert property ( !$isunknown({data,ctrl}) )
    else $error("mux_2to1: X/Z on inputs");

  // Stage propagation: after k delta cycles, stagek mirrors initial inputs
  ap_stage1: assert property ( 1'b1 |-> ##0 (stage1_data == $past(data,0) && stage1_ctrl == $past(ctrl,0)) )
    else $error("mux_2to1: stage1 mismatch");
  ap_stage2: assert property ( 1'b1 |-> ##0 ##0 (stage2_data == $past(data,0) && stage2_ctrl == $past(ctrl,0)) )
    else $error("mux_2to1: stage2 mismatch");
  ap_stage3: assert property ( 1'b1 |-> ##0 ##0 ##0 (stage3_data == $past(data,0) && stage3_ctrl == $past(ctrl,0)) )
    else $error("mux_2to1: stage3 mismatch");
  ap_stage4: assert property ( 1'b1 |-> ##0 ##0 ##0 ##0 (stage4_data == $past(data,0) && stage4_ctrl == $past(ctrl,0)) )
    else $error("mux_2to1: stage4 mismatch");

  // Functional correctness at output after full settle (4 stages + output assign = 5 deltas)
  ap_out_func: assert property (
                 1'b1 |-> ##0 ##0 ##0 ##0 ##0
                 ( out == ($past(ctrl,0) ? $past(data[1],0) : $past(data[0],0)) )
               )
    else $error("mux_2to1: out != selected input after settle");

  // Out is driven (not X/Z) after settle when inputs were known
  ap_out_known_after_settle: assert property (
                               !$isunknown({$past(data,0),$past(ctrl,0)}) |-> ##0 ##0 ##0 ##0 ##0 !$isunknown(out)
                             )
    else $error("mux_2to1: out unknown after settle");

  // No glitching on out during the first 4 deltas of a new input event
  ap_out_no_glitch: assert property (
                      1'b1 |-> ##0 (out == $past(out,0))
                                   ##0 (out == $past(out,0))
                                   ##0 (out == $past(out,0))
                                   ##0 (out == $past(out,0))
                    )
    else $error("mux_2to1: out glitches before settle");

  // Out matches stage4 selection at the same settle point
  ap_out_matches_stage4: assert property (
                           1'b1 |-> ##0 ##0 ##0 ##0 ##0
                           ( out == (stage4_ctrl ? stage4_data[1] : stage4_data[0]) )
                         )
    else $error("mux_2to1: out != stage4 selection at settle");

  // Coverage: exercise both select paths to the output
  cp_sel0: cover property ( 1'b1 |-> ##0 ##0 ##0 ##0 ##0 ($past(ctrl,0)==1'b0 && out == $past(data[0],0)) );
  cp_sel1: cover property ( 1'b1 |-> ##0 ##0 ##0 ##0 ##0 ($past(ctrl,0)==1'b1 && out == $past(data[1],0)) );
endmodule

bind mux_2to1 mux_2to1_sva m_mux_2to1_sva();