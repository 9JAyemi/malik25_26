// SVA for gen_test3
module gen_test3_sva (
  input       [3:0] a, b,
  input             sel,
  input       [3:0] y, z
);

  // Functional correctness (sample after combinational settles)
  property p_y_mux;  @(a or b or sel) 1 |-> ##0 (y === (sel ? a : b)); endproperty
  property p_z_mux;  @(a or b or sel) 1 |-> ##0 (z === (sel ? b : a)); endproperty
  a_y_mux: assert property (p_y_mux);
  a_z_mux: assert property (p_z_mux);

  // Useful invariant
  a_xor_inv: assert property (@(a or b or sel) 1 |-> ##0 ((y ^ z) === (a ^ b)));

  // No X/Z on outputs if inputs are all known
  a_no_x_out: assert property (@(a or b or sel or y or z)
                               !$isunknown({a,b,sel}) |-> ##0 !$isunknown({y,z}));

  // Coverage
  c_sel0_path:  cover property (@(a or b or sel) (sel==0) ##0 (y===b && z===a));
  c_sel1_path:  cover property (@(a or b or sel) (sel==1) ##0 (y===a && z===b));
  c_sel_rise:   cover property (@(sel) $rose(sel));
  c_sel_fall:   cover property (@(sel) $fell(sel));
  c_eq_case:    cover property (@(a or b or sel) (a===b) ##0 (y===z));
  c_neq_case:   cover property (@(a or b or sel) (a!==b) ##0 (y!==z));

endmodule

// Bind to DUT
bind gen_test3 gen_test3_sva i_gen_test3_sva (.a(a), .b(b), .sel(sel), .y(y), .z(z));