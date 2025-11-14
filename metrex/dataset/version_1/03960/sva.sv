// SVA for digital_circuit: synchronous active-low reset, posedge GATE sampling
module digital_circuit_sva(input logic D, RESET_B, GATE, Q);

  default clocking cb @(posedge GATE); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge GATE) past_valid <= 1'b1;

  // Sanity: no X on RESET_B at sampling edge
  ap_no_x_on_reset: assert property ( !$isunknown(RESET_B) );

  // Synchronous reset dominates: if RESET_B==0 at a clock, Q is 0 until next clock
  ap_sync_reset_clears: assert property ( past_valid && !RESET_B |=> (Q == 1'b0) );

  // Normal capture: if RESET_B==1 at a clock, Q == sampled D on the next cycle
  ap_data_capture: assert property ( past_valid && RESET_B |=> (Q == $past(D)) );

  // If sampling known D with reset high, Q must not go X
  ap_no_x_when_known_sample: assert property ( past_valid && RESET_B && !$isunknown($past(D)) |=> !$isunknown(Q) );

  // Q must change only on a GATE posedge (no glitches between clocks)
  always @(Q) ap_q_changes_only_on_gate: assert ($rose(GATE));

  // Coverage: exercise reset path and both data values
  cp_reset_taken: cover property ( past_valid && !RESET_B |=> (Q == 1'b0) );
  cp_capture_0:   cover property ( past_valid && RESET_B && D == 1'b0 |=> (Q == 1'b0) );
  cp_capture_1:   cover property ( past_valid && RESET_B && D == 1'b1 |=> (Q == 1'b1) );

endmodule

bind digital_circuit digital_circuit_sva(.D(D), .RESET_B(RESET_B), .GATE(GATE), .Q(Q));