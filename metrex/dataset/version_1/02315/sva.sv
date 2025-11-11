// SVA for sky130_fd_sc_ms__o31ai
// Bind this to the DUT to check function and provide concise coverage.

module sky130_fd_sc_ms__o31ai_sva (
  input logic Y,
  input logic A1, A2, A3, B1
);
  default clocking cb @(*); endclocking

  // Functional equivalence (4-state accurate)
  a_func: assert property (Y === ~(B1 & (A1 | A2 | A3)));

  // Deterministic corner cases and X-safety
  a_b1_low_forces_one:    assert property (B1 === 1'b0 |-> Y === 1'b1);
  a_all_a_zero_one:       assert property ((A1===1'b0 && A2===1'b0 && A3===1'b0) |-> Y === 1'b1);
  a_b1_and_any_a_one:     assert property ((B1===1'b1 && (A1===1'b1 || A2===1'b1 || A3===1'b1)) |-> Y === 1'b0);
  a_known_inputs_known_y: assert property (!$isunknown({A1,A2,A3,B1}) |-> !$isunknown(Y));

  // Single-input toggle sanity (others known)
  a_b1_rise: assert property ($rose(B1) && !$isunknown({A1,A2,A3})
                              |-> Y === ~(1'b1 & (A1|A2|A3)));
  a_b1_fall: assert property ($fell(B1) && !$isunknown({A1,A2,A3})
                              |-> Y === ~(1'b0 & (A1|A2|A3)));
  a_a1_rise: assert property ($rose(A1) && !$isunknown({A2,A3,B1})
                              |-> Y === ~(B1 & (1'b1 | A2 | A3)));
  a_a1_fall: assert property ($fell(A1) && !$isunknown({A2,A3,B1})
                              |-> Y === ~(B1 & (1'b0 | A2 | A3)));
  a_a2_rise: assert property ($rose(A2) && !$isunknown({A1,A3,B1})
                              |-> Y === ~(B1 & (A1 | 1'b1 | A3)));
  a_a2_fall: assert property ($fell(A2) && !$isunknown({A1,A3,B1})
                              |-> Y === ~(B1 & (A1 | 1'b0 | A3)));
  a_a3_rise: assert property ($rose(A3) && !$isunknown({A1,A2,B1})
                              |-> Y === ~(B1 & (A1 | A2 | 1'b1)));
  a_a3_fall: assert property ($fell(A3) && !$isunknown({A1,A2,B1})
                              |-> Y === ~(B1 & (A1 | A2 | 1'b0)));

  // Coverage: key truth cases and toggles
  c_b1_zero:         cover property (B1==1'b0 && Y==1'b1);
  c_b1_one_a_any:    cover property (B1==1'b1 && (A1|A2|A3)==1'b1 && Y==1'b0);
  c_b1_one_a_none:   cover property (B1==1'b1 && (A1|A2|A3)==1'b0 && Y==1'b1);
  c_tog_b1:          cover property ($changed(B1));
  c_tog_a1:          cover property ($changed(A1));
  c_tog_a2:          cover property ($changed(A2));
  c_tog_a3:          cover property ($changed(A3));
endmodule

bind sky130_fd_sc_ms__o31ai sky130_fd_sc_ms__o31ai_sva o31ai_sva_i (.*);