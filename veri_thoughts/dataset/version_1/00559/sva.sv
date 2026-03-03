// SVA for dff_posedge_reset
module dff_posedge_reset_sva(input logic CLK, D, reset, Q);

  // Sample on all controlling events so we can relate reset deassert to next clk
  default clocking cb @(posedge CLK or posedge reset or negedge reset); endclocking

  // Async reset clears immediately and dominates
  ap_async_rst_clear: assert property ( $rose(reset) |-> ##0 (Q == 1'b0) );

  // While reset is asserted, Q stays low (checked at all controlling events)
  ap_q_low_during_reset: assert property ( reset |-> (Q == 1'b0) );

  // On posedge CLK when not in reset, Q reflects the previously-sampled D
  ap_capture_d: assert property ( ($rose(CLK) && !reset) |-> (Q == $past(D)) );

  // After reset deasserts, Q must remain 0 until the next posedge CLK
  ap_hold_zero_until_clk_after_deassert:
    assert property ( $fell(reset) |-> (Q == 1'b0) until_with $rose(CLK) );

  // Basic X checks around controlling events
  ap_q_known_after_events:
    assert property ( (($rose(CLK) && !reset) || $rose(reset)) |-> ##0 !$isunknown(Q) );
  ap_d_known_when_sampled:
    assert property ( ($rose(CLK) && !reset) |-> !$isunknown(D) );

  // Coverage
  cp_reset_pulse:           cover property ( $rose(reset) ##[1:$] $fell(reset) );
  cp_normal_capture:        cover property ( ($rose(CLK) && !reset) && (Q == $past(D)) );
  cp_clk_and_reset_same_ts: cover property ( $rose(reset) && $rose(CLK) );

endmodule

// Example bind (optional):
// bind dff_posedge_reset dff_posedge_reset_sva sva_inst(.CLK(CLK), .D(D), .reset(reset), .Q(Q));