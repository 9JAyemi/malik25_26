// SVA checker for binary_adder. Bind/connect clk/rst_n from your environment.
module binary_adder_sva #(
  parameter W = 8
)(
  input  logic                   clk,
  input  logic                   rst_n,

  // DUT ports
  input  logic [W-1:0]           input1,
  input  logic [W-1:0]           input2,
  input  logic                   carry_in,
  input  logic [W-1:0]           sum,
  input  logic                   carry_out,
  input  logic                   overflow_flag,

  // DUT internals (bind via hierarchical connections)
  input  logic [W:0]             stage1_out,
  input  logic [W:0]             stage2_out,
  input  logic [W:0]             stage3_out,
  input  logic [W:0]             stage4_out,
  input  logic [W:0]             stage5_out,
  input  logic [W:0]             stage6_out,
  input  logic [W:0]             stage7_out,
  input  logic [W+1:0]           stage8_out,
  input  logic [1:0]             overflow_check
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Common helpers
  localparam int SUMW = W+1;
  // 9-bit golden sum
  function automatic logic [SUMW-1:0] gold_sum(input logic [W-1:0] a, b, input logic cin);
    return {1'b0,a} + {1'b0,b} + cin;
  endfunction

  // 1) Functional correctness: sum/carry
  assert property ( {carry_out, sum} == gold_sum(input1, input2, carry_in) )
    else $error("Adder mismatch: {{co,sum}} != a+b+cin");

  // 2) Functional correctness: overflow (two's-complement overflow)
  assert property ( overflow_flag == ((input1[W-1] == input2[W-1]) && (sum[W-1] != input1[W-1])) )
    else $error("Overflow flag incorrect");

  // 3) Connectivity to final stage
  assert property ( sum == stage8_out[W-1:0] && carry_out == stage8_out[W] )
    else $error("Output not sourced from stage8_out");

  // 4) Sizing sanity: stage8_out MSB should be 0 (due to RHS sizing in RTL)
  assert property ( stage8_out[W+1] == 1'b0 )
    else $error("Unexpected set of stage8_out[%0d]", W+1);

  // 5) No X/Z on outputs when inputs are known
  assert property ( !$isunknown({input1,input2,carry_in}) |-> !$isunknown({sum,carry_out,overflow_flag}) )
    else $error("Outputs contain X/Z for known inputs");

  // 6) Internal pipes should not be X/Z (helps catch comb loops/width issues)
  assert property ( !$isunknown({stage1_out,stage2_out,stage3_out,stage4_out,stage5_out,stage6_out,stage7_out,stage8_out,overflow_check}) )
    else $error("Internal stages contain X/Z");

  // 7) Identity and key algebraic corner-cases
  assert property ( (input2 == '0 && !carry_in) |-> (sum == input1 && !carry_out && !overflow_flag) )
    else $error("Identity a+0+0 failed");

  assert property ( (input1 == '0 && !carry_in) |-> (sum == input2 && !carry_out && !overflow_flag) )
    else $error("Identity 0+b+0 failed");

  assert property ( (input2 == ~input1 && carry_in) |-> (sum == '0 && carry_out && !overflow_flag) )
    else $error("a + ~a + 1 property failed");

  // 8) Coverage: carry, overflow, and key edges
  cover property ( carry_out );
  cover property ( overflow_flag );

  // Positive overflow: 0x7F + 0x01 -> 0x80
  cover property ( input1 == 8'h7F && input2 == 8'h01 && !carry_in && overflow_flag );

  // Negative overflow: 0x80 + 0x80 -> 0x00 with overflow
  cover property ( input1 == 8'h80 && input2 == 8'h80 && !carry_in && overflow_flag );

  // Identity cover
  cover property ( input2 == '0 && !carry_in && sum == input1 && !carry_out && !overflow_flag );

  // Invert+carry cover
  cover property ( input2 == ~input1 && carry_in && sum == '0 && carry_out && !overflow_flag );

endmodule

// Example bind (connect clk/rst_n from your env, and map internals by name):
// bind binary_adder binary_adder_sva #(.W(8)) u_bin_add_sva (
//   .clk(clk), .rst_n(rst_n),
//   .input1(input1), .input2(input2), .carry_in(carry_in),
//   .sum(sum), .carry_out(carry_out), .overflow_flag(overflow_flag),
//   .stage1_out(stage1_out), .stage2_out(stage2_out), .stage3_out(stage3_out),
//   .stage4_out(stage4_out), .stage5_out(stage5_out), .stage6_out(stage6_out),
//   .stage7_out(stage7_out), .stage8_out(stage8_out), .overflow_check(overflow_check)
// );