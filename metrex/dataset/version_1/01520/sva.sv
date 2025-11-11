// SVA for Span12Mux_v0
// Concise, high-quality checks and coverage for all behaviors

bind Span12Mux_v0 Span12Mux_v0_sva i_Span12Mux_v0_sva(.I(I), .S(S), .O(O));

module Span12Mux_v0_sva(input [11:0] I, input [3:0] S, input [11:0] O);

  // Sample on any activity of inputs/outputs; use ##0 to see NBA-updated O
  default clocking cb @(I or S or O); endclocking

  // Functional equivalence (4-state): O mirrors I for S in [0:11], else 0
  property p_functional_4state;
    1'b1 |-> ##0 (O === ((S inside {[4'd0:4'd11]}) ? I : 12'h000));
  endproperty
  assert property (p_functional_4state)
    else $error("Span12Mux_v0: functional mismatch: S=%0d I=%h O=%h", S, I, O);

  // X-safety: when S is known and selects pass-through, known I implies known O==I
  property p_known_passthrough;
    (!$isunknown(S) && (S inside {[4'd0:4'd11]}) && !$isunknown(I))
      |-> ##0 (O == I);
  endproperty
  assert property (p_known_passthrough)
    else $error("Span12Mux_v0: O must equal I without X when S in [0:11] and I known");

  // X-safety: when S is known and in default, O must be exactly 0 (no X/Z)
  property p_known_default_zero;
    (!$isunknown(S) && !(S inside {[4'd0:4'd11]}))
      |-> ##0 (O == 12'h000);
  endproperty
  assert property (p_known_default_zero)
    else $error("Span12Mux_v0: O must be 0 when S in [12:15]");

  // Change-causality: any O change must be caused by I or S change
  property p_o_change_has_cause;
    $changed(O) |-> ($changed(S) || ((S inside {[4'd0:4'd11]}) && $changed(I)));
  endproperty
  assert property (p_o_change_has_cause)
    else $error("Span12Mux_v0: O changed without a corresponding I/S cause");

  // Functional coverage: hit every S value and its expected behavior
  genvar k;
  generate
    for (k = 0; k < 12; k++) begin : C_PASS
      cover property ( (S == k) ##0 (O === I) );
    end
  endgenerate
  generate
    for (k = 12; k < 16; k++) begin : C_DEF
      cover property ( (S == k) ##0 (O == 12'h000) );
    end
  endgenerate

  // Cross-coverage of transitions into and out of default range
  cover property ( (S inside {[4'd0:4'd11]}) ##1 (S inside {[4'd12:4'd15]}) ##0 (O == 12'h000) );
  cover property ( (S inside {[4'd12:4'd15]}) ##1 (S inside {[4'd0:4'd11]}) ##0 (O === I) );

endmodule