// SVA for ripple_carry_adder and full_adder
// Bind these modules in your TB and drive clk/rst_n.
// Example:
//   bind ripple_carry_adder rca_sva #(.W(4)) rca_chk(.clk(tb_clk), .rst_n(tb_rst_n));
//   bind full_adder        fa_sva             fa_chk(.clk(tb_clk), .rst_n(tb_rst_n));

module rca_sva #(parameter int W=4) (
  input logic clk,
  input logic rst_n
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  function automatic logic carry3(logic a,b,cin);
    return (a & b) | (a & cin) | (b & cin);
  endfunction

  // Functional correctness and X checks
  ap_add_correct_known: assert property (
    !$isunknown({in0,in1,carry_in}) |-> (!$isunknown({sum,carry_out}) &&
                                         {carry_out,sum} == in0 + in1 + carry_in)
  );
  ap_add_correct:       assert property ( {carry_out,sum} == in0 + in1 + carry_in );

  // Per-bit stage checks (ripple and taps)
  ap_b0_sum:   assert property ( sum[0] == (in0[0] ^ in1[0] ^ carry_in) );
  ap_b0_carry: assert property ( stage1_carry == carry3(in0[0], in1[0], carry_in) );
  ap_b0_tap:   assert property ( sum[0] == stage1_sum[0] );

  ap_b1_sum:   assert property ( sum[1] == (in0[1] ^ in1[1] ^ stage1_carry) );
  ap_b1_carry: assert property ( stage2_carry == carry3(in0[1], in1[1], stage1_carry) );
  ap_b1_tap:   assert property ( sum[1] == stage2_sum[1] );

  ap_b2_sum:   assert property ( sum[2] == (in0[2] ^ in1[2] ^ stage2_carry) );
  ap_b2_carry: assert property ( stage3_carry == carry3(in0[2], in1[2], stage2_carry) );
  ap_b2_tap:   assert property ( sum[2] == stage3_sum[2] );

  ap_b3_sum:   assert property ( sum[3] == (in0[3] ^ in1[3] ^ stage3_carry) );
  ap_b3_carry: assert property ( carry_out   == carry3(in0[3], in1[3], stage3_carry) );

  // No-X propagation on used nodes when drivers are known
  ax_b0_known: assert property ( !$isunknown({in0[0],in1[0],carry_in})
                                 |-> !$isunknown({stage1_sum[0],stage1_carry,sum[0]}) );
  ax_b1_known: assert property ( !$isunknown({in0[1],in1[1],stage1_carry})
                                 |-> !$isunknown({stage2_sum[1],stage2_carry,sum[1]}) );
  ax_b2_known: assert property ( !$isunknown({in0[2],in1[2],stage2_carry})
                                 |-> !$isunknown({stage3_sum[2],stage3_carry,sum[2]}) );
  ax_b3_known: assert property ( !$isunknown({in0[3],in1[3],stage3_carry})
                                 |-> !$isunknown({sum[3],carry_out}) );

  // Concise functional coverage
  cp_zero:          cover property ( in0=='0 && in1=='0 && !carry_in && sum=='0 && !carry_out );
  cp_cout1:         cover property ( carry_out );
  cp_overflow_eq:   cover property ( {carry_out,sum} == in0 + in1 + carry_in && carry_out );
  cp_any_propagate: cover property ( (in0 ^ in1) != '0 );
  cp_any_generate:  cover property ( (in0 & in1) != '0 );
  cp_any_kill:      cover property ( (~in0 & ~in1) != '0 );
  cp_full_ripple:   cover property ( ((in0 ^ in1) == {W{1'b1}}) && carry_in && (sum=='0) && carry_out );
endmodule


module fa_sva (
  input logic clk,
  input logic rst_n
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  a_sum:  assert property ( sum == (a ^ b ^ carry_in) );
  a_cout: assert property ( carry_out == ((a & b) | (a & carry_in) | (b & carry_in)) );
  ax_no_x: assert property ( !$isunknown({a,b,carry_in}) |-> !$isunknown({sum,carry_out}) );

  // Minimal FA coverage: propagate, generate, kill seen
  c_prop: cover property ( (a ^ b) && carry_in );
  c_gen:  cover property ( (a & b) );
  c_kill: cover property ( (~a & ~b) && !carry_in );
endmodule