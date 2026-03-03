// SVA for d_ff_reset: async active-low reset, posedge clocked DFF
module d_ff_reset_sva #(parameter int unsigned RECOVERY_CYCLES = 1) (
  input logic D,
  input logic RESET_B,
  input logic CLK,
  input logic Q
);

  // Q goes low immediately on async reset assert; stays low while in reset
  ap_async_reset_immediate: assert property ( $fell(RESET_B) |-> ##0 (Q==1'b0) );
  ap_reset_holds_Q_low:    assert property ( !RESET_B |-> (Q==1'b0) );

  // After reset deassert, Q must remain 0 until the next clock edge
  ap_q_zero_until_clk_after_release: assert property ( $rose(RESET_B) |-> (Q==1'b0 until_with $rose(CLK)) );

  // On posedge CLK with reset deasserted, Q captures D (check in NBA/postponed with ##0)
  ap_capture_on_clk: assert property ( @(posedge CLK) RESET_B |-> ##0 (Q == $past(D)) );

  // Data must be known when sampled; Q changes only on allowed events
  ap_d_known_at_sample:         assert property ( @(posedge CLK) RESET_B |-> !$isunknown(D) );
  ap_q_changes_only_on_events:  assert property ( $changed(Q) |-> ($rose(CLK) || $fell(RESET_B)) );

  // Optional recovery: require RESET_B high for RECOVERY_CYCLES prior clocks before sampling
  ap_recovery_cycles: assert property ( @(posedge CLK) disable iff (!RESET_B)
                                       $past(RESET_B, RECOVERY_CYCLES) );

  // Coverage
  cv_reset_assert:   cover property ( $fell(RESET_B) );
  cv_reset_deassert: cover property ( $rose(RESET_B) );
  cv_capture_any:    cover property ( @(posedge CLK) RESET_B ##0 (Q==D) );
  cv_q_rise:         cover property ( @(posedge CLK) RESET_B ##0 $rose(Q) );
  cv_q_fall:         cover property ( @(posedge CLK) RESET_B ##0 $fell(Q) );
  cv_cap_one:        cover property ( @(posedge CLK) RESET_B && (D==1) ##0 (Q==1) );
  cv_cap_zero:       cover property ( @(posedge CLK) RESET_B && (D==0) ##0 (Q==0) );

endmodule

bind d_ff_reset d_ff_reset_sva sva_i (.*);