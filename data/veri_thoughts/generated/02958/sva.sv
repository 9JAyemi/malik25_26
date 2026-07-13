module and_gate_sva (
  input logic A,
  input logic B,
  input logic CLK,
  input logic RST,
  input logic Y
);
  // While reset is asserted (active-low), Y must be 0 at each clock edge.
  reset_drives_Y_low: assert property (
    @(posedge CLK) !RST |-> (Y == 1'b0)
  );

  // Out of reset, Y equals the previous cycle's A & B.
  y_equals_past_and: assert property (
    @(posedge CLK) disable iff (!RST) $past(RST) |-> (Y == $past(A & B))
  );

  // If previous cycle had A=1 and B=1, then Y must be 1 this cycle.
  y1_when_prev_inputs_11: assert property (
    @(posedge CLK) disable iff (!RST) $past(RST) && $past(A) && $past(B) |-> (Y == 1'b1)
  );

  // If previous cycle had A=0 (regardless of B), then Y must be 0 this cycle.
  y0_when_prev_A0: assert property (
    @(posedge CLK) disable iff (!RST) $past(RST) && ($past(A) == 1'b0) |-> (Y == 1'b0)
  );

  // If previous cycle had B=0 (regardless of A), then Y must be 0 this cycle.
  y0_when_prev_B0: assert property (
    @(posedge CLK) disable iff (!RST) $past(RST) && ($past(B) == 1'b0) |-> (Y == 1'b0)
  );

  // A rising Y implies previous cycle's (A & B) was 1.
  y_rise_implies_prev_and1: assert property (
    @(posedge CLK) disable iff (!RST) $past(RST) && $rose(Y) |-> ($past(A & B) == 1'b1)
  );

  // A falling Y implies previous cycle's (A & B) was 0.
  y_fall_implies_prev_and0: assert property (
    @(posedge CLK) disable iff (!RST) $past(RST) && $fell(Y) |-> ($past(A & B) == 1'b0)
  );

  // If (A & B) was stable over the last two cycles, Y must equal its previous value.
  y_stable_when_inputs_stable: assert property (
    @(posedge CLK) disable iff (!RST) $past(RST,2) && ($past(A & B,2) == $past(A & B,1)) |-> (Y == $past(Y))
  );
endmodule