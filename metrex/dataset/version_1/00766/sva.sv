// SVA for MUXF7: concise, high-quality checks and coverage.
// Bind example: bind MUXF7 MUXF7_sva u_muxf7_sva (.O(O), .I0(I0), .I1(I1), .S(S));

module MUXF7_sva (input logic O, I0, I1, S);

  // Functional correctness whenever all inputs are known (no X/Z)
  property p_mux_func_known;
    @(posedge I0 or negedge I0 or posedge I1 or negedge I1 or posedge S or negedge S)
      (!$isunknown({I0,I1,S})) |-> ##0 (O === (S ? I1 : I0));
  endproperty
  assert property (p_mux_func_known);

  // Output must be known when inputs are known
  assert property (@(posedge I0 or negedge I0 or posedge I1 or negedge I1 or posedge S or negedge S)
                   (!$isunknown({I0,I1,S})) |-> ##0 !$isunknown(O));

  // No spurious O change without an input or select change
  assert property (@(posedge O or negedge O) ($changed(I0) || $changed(I1) || $changed(S)));

  // Select-specific response on data changes (when selected and known)
  assert property (@(posedge I0 or negedge I0) (S===1'b0 && !$isunknown(I0)) |-> ##0 (O===I0));
  assert property (@(posedge I1 or negedge I1) (S===1'b1 && !$isunknown(I1)) |-> ##0 (O===I1));

  // Response to select changes (when data known)
  assert property (@(posedge S) (!$isunknown({I0,I1})) |-> ##0 (O===I1));
  assert property (@(negedge S) (!$isunknown({I0,I1})) |-> ##0 (O===I0));

  // Coverage: exercise both data paths and select switching
  cover property (@(posedge I0 or negedge I0) (S===1'b0 && !$isunknown(I0) && O===I0));
  cover property (@(posedge I1 or negedge I1) (S===1'b1 && !$isunknown(I1) && O===I1));
  cover property (@(posedge S) (!$isunknown({I0,I1}) && O===I1));
  cover property (@(negedge S) (!$isunknown({I0,I1}) && O===I0));

  // Coverage: observe X-optimism scenario (S is X and data differ) — model chooses I0 in this RTL
  cover property (@(posedge I0 or negedge I0 or posedge I1 or negedge I1)
                  (S===1'bx && (I0!==I1) && O===I0));

endmodule