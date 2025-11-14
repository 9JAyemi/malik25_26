// SVA checker for sum_diff. Bind this to the DUT.
module sum_diff_sva #(parameter int W = 8) (
  input logic [W-1:0] A,
  input logic [W-1:0] B,
  input logic [W-1:0] S,
  input logic [W-1:0] D
);
  // Sample on any change of inputs/outputs
  event ev;
  always @(A or B or S or D) -> ev;

  // Wide refs to capture carry/borrow
  logic [W:0] sum9, diff9;
  assign sum9  = {1'b0, A} + {1'b0, B};
  assign diff9 = {1'b0, A} - {1'b0, B};

  // Functional correctness (for known inputs)
  assert property (@(ev) (!$isunknown({A,B})) |-> ##0
                    (S == sum9[W-1:0] && D == diff9[W-1:0]))
    else $error("sum_diff: functional mismatch");

  // Outputs must not be X/Z when inputs are known
  assert property (@(ev) (!$isunknown({A,B})) |-> ##0
                    !$isunknown({S,D}))
    else $error("sum_diff: X/Z on outputs with known inputs");

  // No spurious output toggles when inputs are stable
  assert property (@(ev) $stable({A,B}) |-> ##0 $stable({S,D}))
    else $error("sum_diff: outputs changed without input change");

  // Coverage: carry, borrow, zeros, and corners
  cover property (@(ev) $changed({A,B}) && sum9[W]);           // add carry-out
  cover property (@(ev) $changed({A,B}) && diff9[W]);          // sub borrow-out
  cover property (@(ev) $changed({A,B}) && (S == '0));         // sum is zero
  cover property (@(ev) $changed({A,B}) && (D == '0));         // diff is zero (A==B)
  cover property (@(ev) (A == '0    && B == '0));
  cover property (@(ev) (A == '0    && B == {W{1'b1}}));
  cover property (@(ev) (A == {W{1'b1}} && B == '0));
  cover property (@(ev) (A == {W{1'b1}} && B == {W{1'b1}}));
endmodule

// Bind to the DUT
bind sum_diff sum_diff_sva #(.W(8)) u_sum_diff_sva (.*);