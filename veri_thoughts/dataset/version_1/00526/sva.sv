// SVA for DFF and SNPS_CLOCK_GATE_HIGH_Up_counter_COUNTER_WIDTH4
// Focused, concise checks with essential coverage

// Assertions for the generic DFF
module DFF_sva (input logic CLK, D, Q);

  // Functional capture: Q reflects D from previous CLK edge
  property p_dff_captures_D;
    @(posedge CLK) Q === $past(D);
  endproperty
  assert property (p_dff_captures_D);

  // Knownness on clock edge (avoid X/Z propagating through flop)
  assert property (@(posedge CLK) !$isunknown({D,Q}));

  // Coverage: both transitions propagate through the flop
  cover property (@(posedge CLK) $rose(D) ##1 $rose(Q));
  cover property (@(posedge CLK) $fell(D) ##1 $fell(Q));

endmodule

bind DFF DFF_sva dff_sva_i (.CLK(CLK), .D(D), .Q(Q));


// Assertions for the clock-gate wrapper
module SNPS_CLOCK_GATE_HIGH_Up_counter_COUNTER_WIDTH4_sva (
  input  logic CLK, EN, TE, ENCLK,
  input  logic ENCLK_blocking_assign
);

  // The internal DFF must capture EN on CLK
  property p_en_is_registered;
    @(posedge CLK) ENCLK_blocking_assign === $past(EN);
  endproperty
  assert property (p_en_is_registered);

  // Combinational gating function must hold at all times
  assert property (ENCLK === (TE ? ENCLK_blocking_assign : 1'b0));

  // TE semantics (redundant with above, but clearer intent)
  assert property ( (TE == 1'b0) |-> (ENCLK == 1'b0) );
  assert property ( (TE == 1'b1) |-> (ENCLK === ENCLK_blocking_assign) );

  // No X on output when inputs are known
  assert property ( (!$isunknown({TE, ENCLK_blocking_assign})) |-> !$isunknown(ENCLK) );

  // Coverage:
  // - With TE high, EN rising/falling at CLK propagates to ENCLK on next CLK
  cover property (@(posedge CLK) TE && $rose(EN) ##1 $rose(ENCLK));
  cover property (@(posedge CLK) TE && $fell(EN) ##1 $fell(ENCLK));

  // - TE 0->1 immediately exposes the registered enable to ENCLK
  cover property ( (TE==1'b0 && ENCLK_blocking_assign==1'b1) ##1 (TE==1'b1 && ENCLK==1'b1) );
  cover property ( (TE==1'b0 && ENCLK_blocking_assign==1'b0) ##1 (TE==1'b1 && ENCLK==1'b0) );

endmodule

bind SNPS_CLOCK_GATE_HIGH_Up_counter_COUNTER_WIDTH4
  SNPS_CLOCK_GATE_HIGH_Up_counter_COUNTER_WIDTH4_sva cg_sva_i
  (.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK), .ENCLK_blocking_assign(ENCLK_blocking_assign));