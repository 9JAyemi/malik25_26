// SVA for add_sub_edge and internal behavior
module add_sub_edge_sva (
  input  logic        clk,
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        sub,
  input  logic [7:0]  in,
  input  logic [31:0] sum,
  input  logic [7:0]  anyedge_result,

  // internal signals
  input  logic [31:0] adder_out,
  input  logic [31:0] inverted_b,
  input  logic [7:0]  prev_in,
  input  logic [7:0]  anyedge_out
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [31:0] twos_b(input logic s, input logic [31:0] bb);
    return s ? (~bb + 32'd1) : bb;
  endfunction

  // Structure checks
  a_inversion_a:      assert property (inverted_b == twos_b(sub, b)) else $error("inverted_b mismatch");
  sum_passthrough_a:  assert property (sum == adder_out) else $error("sum != adder_out");
  anyedge_def_a:      assert property (!$isunknown(prev_in) |-> anyedge_out == (in ^ prev_in)) else $error("anyedge_out mismatch");

  // Functional correctness of add/sub (32-bit wrap)
  addsub_func_a:      assert property (sum == (a + twos_b(sub, b))) else $error("sum functional mismatch");

  // prev_in captures last in
  prev_in_cap_a:      assert property (!$isunknown($past(in)) |-> prev_in == $past(in)) else $error("prev_in not capturing in");

  // anyedge_result gating
  edge_zero_a:        assert property (!$isunknown(prev_in) && (in == $past(in)) |-> anyedge_result == 8'h00) else $error("anyedge_result should be 0 when no edge");
  edge_sum_a:         assert property (!$isunknown(prev_in) && (in != $past(in)) |-> anyedge_result == sum[7:0]) else $error("anyedge_result should equal sum[7:0] on any edge");

  // No X on outputs when inputs known
  known_outs_a:       assert property (!$isunknown({a,b,sub,in}) |-> !$isunknown({sum, anyedge_result})) else $error("Outputs X with known inputs");

  // Coverage
  cover_add_c:        cover property (sub==1'b0);
  cover_sub_c:        cover property (sub==1'b1);
  cover_no_edge_c:    cover property (!$isunknown(prev_in) && (in == $past(in)));
  cover_one_bit_edge: cover property (!$isunknown(prev_in) && $onehot(in ^ $past(in)));
  cover_multi_edge:   cover property (!$isunknown(prev_in) && ($countones(in ^ $past(in)) > 1));
  cover_add_wrap:     cover property (a==32'hFFFF_FFFF && b==32'h0000_0001 && sub==1'b0 && sum==32'h0000_0000);
  cover_sub_wrap:     cover property (a==32'h0000_0000 && b==32'h0000_0001 && sub==1'b1 && sum==32'hFFFF_FFFF);
endmodule

bind add_sub_edge add_sub_edge_sva add_sub_edge_sva_i(
  .clk(clk),
  .a(a), .b(b), .sub(sub), .in(in),
  .sum(sum), .anyedge_result(anyedge_result),
  .adder_out(adder_out),
  .inverted_b(inverted_b),
  .prev_in(prev_in),
  .anyedge_out(anyedge_out)
);