// SVA for top_module — concise, high-quality checks and coverage
`ifndef SYNTHESIS
module top_module_sva (
  input logic        clk,
  input logic [3:0]  A, B,
  input logic        select,
  input logic [3:0]  sum,
  input logic [3:0]  sum1, sum2,
  input logic        enable1, enable2
);
  default clocking cb @(posedge clk); endclocking

  // Control logic correctness
  a_enable1_def:   assert property (enable1 == ~select);
  a_enable2_def:   assert property (enable2 ==  select);
  a_en_onehot:     assert property (enable1 ^ enable2);

  // Adder correctness and consistency
  a_adder1_func:   assert property (sum1 == (A + B));        // 4-bit truncation
  a_adder2_func:   assert property (sum2 == (A + B));
  a_adders_equal:  assert property (sum1 == sum2);

  // Mux/output correctness
  a_mux_sel0:      assert property (!select |-> sum == sum1);
  a_mux_sel1:      assert property ( select |-> sum == sum2);
  a_sum_mod16:     assert property (sum == (A + B));          // overall output correctness

  // Select toggle must not affect sum if A,B stable (both adders identical)
  a_sel_toggle_no_glitch: assert property ($stable({A,B}) && $changed(select) |-> $stable(sum));

  // Known-propagation: known inputs imply known internal/outputs
  a_known_paths:   assert property (! $isunknown({A,B,select}) |-> ! $isunknown({sum,sum1,sum2,enable1,enable2}));

  // Functional coverage
  c_sel0:          cover property (!select);
  c_sel1:          cover property ( select);
  c_sel_toggle:    cover property ($stable({A,B}) ##1 $changed(select));
  c_overflow:      cover property (({1'b0,A}+{1'b0,B})[4]);   // carry-out
  c_zero:          cover property (A==4'd0  && B==4'd0  && sum==4'd0);
  c_max:           cover property (A==4'd15 && B==4'd15 && sum==4'hE); // 15+15=30 -> 14 (mod 16)
endmodule

// Bind into DUT (accesses internal nets sum1,sum2,enable1,enable2)
bind top_module top_module_sva sva_i (
  .clk(clk),
  .A(A), .B(B),
  .select(select),
  .sum(sum),
  .sum1(sum1), .sum2(sum2),
  .enable1(enable1), .enable2(enable2)
);
`endif