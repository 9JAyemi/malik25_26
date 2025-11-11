// Bindable SVA checker for carry_save_adder
bind carry_save_adder carry_save_adder_sva sva();

module carry_save_adder_sva;

  default clocking cb @(posedge clk); endclocking

  // Helpers
  function automatic logic [3:0] exp_p3(input logic [3:0] a, b, c);
    exp_p3 = (a ^ b) ^ c ^ (a & b);
  endfunction

  function automatic logic [3:0] exp_g3(input logic [3:0] a, b, c);
    exp_g3 = ((a ^ b) ^ c) & (a & b);
  endfunction

  function automatic logic [4:0] u5(input logic [3:0] x);
    u5 = {1'b0, x};
  endfunction

  // Registered outputs must match the intended combinational functions (1-cycle latency)
  a_reg_matches_func: assert property (
    disable iff ($isunknown({a,b,c,s,c_out}))
    (s == $past(exp_p3(a,b,c))) && (c_out == $past(exp_g3(a,b,c)))
  ) else $error("carry_save_adder: registered outputs do not match expected functions");

  // Registered outputs must match the DUT's internal comb nets (1-cycle latency)
  a_reg_matches_internal: assert property (
    disable iff ($isunknown({p3,g3,s,c_out}))
    (s == $past(p3)) && (c_out == $past(g3))
  ) else $error("carry_save_adder: s/c_out mismatch vs. internal p3/g3");

  // Internal combinational definitions must hold
  a_internal_comb_defs: assert property (
    disable iff ($isunknown({a,b,c,p1,g1,p2,g2,p3,g3}))
    (p1 == (a ^ b)) && (g1 == (a & b)) &&
    (p2 == (p1 ^ c)) && (g2 == (p1 & c)) &&
    (p3 == (p2 ^ g1)) && (g3 == (p2 & g1))
  ) else $error("carry_save_adder: internal comb definitions violated");

  // Arithmetic CSA spec: a+b+c must equal s + 2*c_out (sampled with 1-cycle latency)
  a_csa_arithmetic: assert property (
    disable iff ($isunknown({a,b,c,s,c_out}))
    (u5(s) + (u5(c_out) << 1)) == $past(u5(a) + u5(b) + u5(c))
  ) else $error("carry_save_adder: arithmetic mismatch: u5(s)+2*u5(c_out) != $past(u5(a)+u5(b)+u5(c))");

  // Outputs must be known whenever inputs are known
  a_no_x_on_outputs: assert property (
    disable iff ($isunknown({a,b,c}))
    !$isunknown({s,c_out})
  ) else $error("carry_save_adder: X/Z detected on outputs with known inputs");

  // Minimal but meaningful coverage
  c_nonzero_carry:    cover property (! $isunknown({a,b,c}) && (|c_out));
  c_all_zero_inputs:  cover property (a==4'h0 && b==4'h0 && c==4'h0);
  c_all_ones_inputs:  cover property (a==4'hF && b==4'hF && c==4'hF);

  genvar i;
  generate
    for (i=0; i<4; i++) begin : cov_bits
      c_sum_bit_1:   cover property (s[i]);
      c_cout_bit_1:  cover property (c_out[i]);
      c_sum_and_cout: cover property (s[i] && c_out[i]);
    end
  endgenerate

endmodule