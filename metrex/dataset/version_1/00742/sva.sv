// SVA for carry_lookahead_adder and top_module
// Focused, high-quality checks and concise coverage

// Bind into DUT to access internal nets p,g,c
module cla_sva;
  // This module is bound into carry_lookahead_adder scope; can reference a,b,sum,p,g,c directly
  default clocking cb @(posedge $global_clock); endclocking

  // Local model
  let exp_p  = a ^ b;
  let exp_g  = a & b;
  let exp_c0 = exp_g[0];
  let exp_c1 = exp_g[1] | (exp_p[1] & exp_g[0]);
  let exp_c2 = exp_g[2] | (exp_p[2] & exp_g[1]) | (exp_p[2] & exp_p[1] & exp_g[0]);
  let exp_c3 = exp_g[3] | (exp_p[3] & exp_g[2]) | (exp_p[3] & exp_p[2] & exp_g[1]) | (exp_p[3] & exp_p[2] & exp_p[1] & exp_g[0]);
  let exp_c  = {exp_c3,exp_c2,exp_c1,exp_c0};
  let exp_sum = {a,b} + {{28{1'b0}}, exp_c};

  // X-prop check
  a_b_known: assert property (!$isunknown({a,b})) |-> !$isunknown({p,g,c,sum}))
    else $error("Unknowns on outputs/internal nets with known inputs");

  // Functional correctness of internal signals
  p_def:  assert property (p == exp_p) else $error("p != a^b");
  g_def:  assert property (g == exp_g) else $error("g != a&b");

  c0_def: assert property (c[0] == exp_c0) else $error("c[0] mismatch");
  c1_def: assert property (c[1] == exp_c1) else $error("c[1] mismatch");
  c2_def: assert property (c[2] == exp_c2) else $error("c[2] mismatch");
  c3_def: assert property (c[3] == exp_c3) else $error("c[3] mismatch");

  // Cross-check c[3] equals carry-out of 4-bit add of a[3:0]+b[3:0]
  c3_add_chk: assert property (c[3] == ({1'b0, a[3:0]} + {1'b0, b[3:0]})[4])
    else $error("c[3] != carry-out of 4-bit add");

  // Sum correctness per DUT intent
  sum_def: assert property (sum == exp_sum) else $error("sum mismatch vs model {a,b}+c");

  // Coverage
  cover_no_carry:        cover property (exp_c == 4'h0);
  cover_full_propagate:  cover property (g[3:1]==3'b000 && p[3:1]==3'b111 && g[0]==1'b1); // long propagate chain
  cover_mid_generate:    cover property (g[2]==1'b1 && p[2]==1'b0); // direct generate at bit2
  // Carry from b into a (overflows 16-bit b when adding c)
  let carry_into_a = ({1'b0, b} + exp_c)[16];
  cover_carry_into_a:    cover property (carry_into_a);

  // Hit all 16 possible c values over time
  genvar i;
  generate for (i=0; i<16; i++) begin : cov_c_vals
    cover_c_val: cover property (exp_c == i[3:0]);
  end endgenerate

endmodule

bind carry_lookahead_adder cla_sva cla_sva_i();

// Optional top-level connectivity/port propagation check
module top_sva;
  default clocking cb @(posedge $global_clock); endclocking
  // In top_module scope; ensure the instance drives the port
  // References instance name 'adder' per provided code
  sum_conn: assert property (sum == adder.sum) else $error("top sum not driven by adder.sum");
  // Simple activity coverage
  cover_sum_changes: cover property ($changed(a) or $changed(b) ##0 $changed(sum));
endmodule

bind top_module top_sva top_sva_i();