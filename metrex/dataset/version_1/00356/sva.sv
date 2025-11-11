// SVA for bitwise_and_func and top_module (bind-style, clockless via $global_clock)

module bitwise_and_func_sva (
  input logic [7:0]  vec1,
  input logic [7:0]  vec2,
  input logic        select,
  input logic [7:0]  and_out,
  input logic [15:0] sum_out
);
  default clocking cb @(posedge $global_clock); endclocking

  // Determinism and X-propagation
  a_no_x_when_inputs_known: assert property (
    !$isunknown({vec1,vec2,select}) |-> ##0 !$isunknown({and_out,sum_out})
  );

  // Bitwise AND behavior
  a_and_sel0: assert property (
    (!$isunknown({vec1,vec2,select}) && select===1'b0) |-> ##0 (and_out == (vec1 & vec2))
  );
  a_and_sel1: assert property (
    (select===1'b1) |-> ##0 (and_out == 8'h00)
  );

  // Sum is zero-extended 8-bit addition (carry is dropped)
  let sum8 = (vec1 + vec2);
  a_sum_match: assert property (
    !$isunknown({vec1,vec2}) |-> ##0 (sum_out == {8'h00, sum8})
  );
  a_sum_upper_zero: assert property ( sum_out[15:8] == 8'h00 );

  // Compact functional coverage
  c_sel0: cover property (select===1'b0);
  c_sel1: cover property (select===1'b1);
  let sum9 = {1'b0,vec1}+{1'b0,vec2};
  c_sum_overflow: cover property (sum9[8]); // 9th-bit carry (would be dropped by DUT)
  c_and_nonzero:  cover property ((select===1'b0) && ((vec1 & vec2)!=8'h00) && (and_out!=8'h00));
endmodule

bind bitwise_and_func bitwise_and_func_sva baf_sva (.*);


// SVA for top_module wiring/behavior (select is tied to 0 in instance)
module top_module_sva (
  input logic [7:0]  vec1,
  input logic [7:0]  vec2,
  input logic [7:0]  outv,
  input logic [15:0] sum
);
  default clocking cb @(posedge $global_clock); endclocking

  a_and_top: assert property (
    !$isunknown({vec1,vec2}) |-> ##0 (outv == (vec1 & vec2))
  );
  let sum8_top = (vec1 + vec2);
  a_sum_top: assert property (
    !$isunknown({vec1,vec2}) |-> ##0 (sum == {8'h00, sum8_top})
  );
  a_sum_upper_zero_top: assert property (sum[15:8] == 8'h00);

  // Minimal coverage
  c_and_nonzero_top:   cover property (((vec1 & vec2)!=8'h00) && (outv!=8'h00));
  c_sum_overflow_top:  cover property (({1'b0,vec1}+{1'b0,vec2})[8]);
endmodule

bind top_module top_module_sva top_sva (.*);