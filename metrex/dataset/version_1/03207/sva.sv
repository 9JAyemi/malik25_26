// SVA for my_module
// Bind this file to the DUT: bind my_module my_module_sva sva_inst (.*);

module my_module_sva (
  input X, A1, A2, B1, C1, VPWR, VGND
);
  default clocking cb @(posedge $global_clock); endclocking

  // Rail sanity (catch tie-off/power issues)
  a_power_levels: assert property (VPWR === 1'b1 && VGND === 1'b0);

  // Functional equivalence when powered and inputs known
  property p_func;
    (VPWR===1'b1 && VGND===1'b0 && !$isunknown({A1,A2,B1,C1}))
      |-> ##0 (X === ((A1 && !B1) || (A2 && !C1)));
  endproperty
  a_func: assert property (p_func);

  // Output must be known when powered and inputs known
  a_no_x_out: assert property (
    (VPWR===1'b1 && VGND===1'b0 && !$isunknown({A1,A2,B1,C1})) |-> ##0 !$isunknown(X)
  );

  // Combinational stability and sensitivity
  a_stable_no_input_change: assert property ($stable({A1,A2,B1,C1}) |-> $stable(X));
  a_change_requires_input:  assert property ($changed(X) |-> $changed({A1,A2,B1,C1}));

  // Useful simplifications under specific conditions (redundant but locally strong)
  a_b1_1:           assert property ((VPWR===1'b1 && VGND===1'b0 && B1===1'b1) |-> ##0 (X === (A2 && !C1)));
  a_c1_1:           assert property ((VPWR===1'b1 && VGND===1'b0 && C1===1'b1) |-> ##0 (X === (A1 && !B1)));
  a_b1_0_c1_0:      assert property ((VPWR===1'b1 && VGND===1'b0 && B1===1'b0 && C1===1'b0) |-> ##0 (X === (A1 || A2)));
  a_b1_1_c1_1:      assert property ((VPWR===1'b1 && VGND===1'b0 && B1===1'b1 && C1===1'b1) |-> ##0 (X === 1'b0));

  // Functional coverage (key cases and toggles)
  c_term1_only:  cover property ((VPWR===1'b1 && VGND===1'b0) && (A1 && !B1) && !(A2 && !C1) && X);
  c_term2_only:  cover property ((VPWR===1'b1 && VGND===1'b0) && (A2 && !C1) && !(A1 && !B1) && X);
  c_both_terms:  cover property ((VPWR===1'b1 && VGND===1'b0) && (A1 && !B1) && (A2 && !C1) && X);
  c_neither:     cover property ((VPWR===1'b1 && VGND===1'b0) && !(A1 && !B1) && !(A2 && !C1) && !X);

  c_rose_X:      cover property ($rose(X));
  c_fell_X:      cover property ($fell(X));
  c_rose_A1:     cover property ($rose(A1));  c_fell_A1: cover property ($fell(A1));
  c_rose_A2:     cover property ($rose(A2));  c_fell_A2: cover property ($fell(A2));
  c_rose_B1:     cover property ($rose(B1));  c_fell_B1: cover property ($fell(B1));
  c_rose_C1:     cover property ($rose(C1));  c_fell_C1: cover property ($fell(C1));

endmodule

bind my_module my_module_sva sva_inst (.*);