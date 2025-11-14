// SVA for binary_multiplier
module binary_multiplier_sva #(parameter int WA=8, WB=8, WR=16)
(
  input logic              clk,
  input logic              reset,
  input logic [WA-1:0]     a,
  input logic [WB-1:0]     b,
  input logic [WR-1:0]     result
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always @(posedge clk) past_valid <= reset ? 1'b0 : 1'b1;

  // Sanity: no X/Z after reset deasserted
  assert property (past_valid |-> !$isunknown({reset,a,b,result}));

  // Reset behavior
  assert property (reset |-> result == '0);
  assert property (reset |=> result == '0);

  // Functional correctness: 1-cycle latency multiply
  assert property (past_valid && !reset |-> result == $past(a) * $past(b));

  // Stability when inputs are stable
  assert property (past_valid && !reset && $stable(a) && $stable(b) |-> $stable(result));

  // Zeroing cases
  assert property (past_valid && !reset && ($past(a) == '0 || $past(b) == '0) |-> result == '0);

  // Coverage: one-hot partial products
  genvar i;
  generate
    for (i=0; i<WA; i++) begin : C_ONEHOT
      cover property (past_valid && !reset &&
                      ($past(a) == (1 << i)) &&
                      (result == ($past(b) << i)));
    end
  endgenerate

  // Coverage: multiple bits set in a (exercise accumulation) and max*max
  cover property (past_valid && !reset && $countones($past(a)) >= 2 &&
                  result == $past(a) * $past(b));
  cover property (past_valid && !reset &&
                  $past(a) == {WA{1'b1}} && $past(b) == {WB{1'b1}} &&
                  result == ({WA{1'b1}} * {WB{1'b1}}));

endmodule

// Bind into DUT
bind binary_multiplier binary_multiplier_sva #(.WA(8), .WB(8), .WR(16)) bm_sva (.*);