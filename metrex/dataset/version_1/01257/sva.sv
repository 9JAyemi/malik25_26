// SVA for func5 and FullAdder
// Assumes a sampling clock `clk` from the environment.
// Bind these checkers to the DUTs.

module func5_sva(input logic clk);
  default clocking cb @(posedge clk); endclocking

  // 1) Local functional checks of each full-adder stage and top-level mapping
  // Base stage: FA0
  assert property (
    !$isunknown({A[25],A[24]}) |->
    (sum[24] == (A[25] ^ A[24]) && c_out[24] == (A[25] & A[24]))
  );

  // Chain stages: FA1..FA23 (produce sum[23:1], c_out[23:1])
  genvar i;
  generate
    for (i=1; i<=23; i++) begin : g_chain
      assert property (
        !$isunknown({sum[i+1], A[i], c_out[i+1]}) |->
        (sum[i] == (sum[i+1] ^ A[i] ^ c_out[i+1]) &&
         c_out[i] == ((sum[i+1] & A[i]) | (c_out[i+1] & (sum[i+1] ^ A[i]))))
      );
    end
  endgenerate

  // Final stage into outputs C[0] and c_out[0]
  assert property (
    !$isunknown({sum[1], A[0], c_out[1]}) |->
    (C[0] == (sum[1] ^ A[0] ^ c_out[1]) &&
     c_out[0] == ((sum[1] & A[0]) | (c_out[1] & (sum[1] ^ A[0]))))
  );

  // Top-level wiring/mapping
  assert property (!$isunknown(sum[24:1]) |->
                   (C[24:1] == sum[24:1]));
  assert property (C[25] == c_out[0]);

  // 2) X-propagation sanity: if A is known, all observable logic is known
  assert property (!$isunknown(A) |-> !$isunknown({C,sum,c_out}));

  // 3) Lightweight functional coverage
  // Extremes and carry behavior
  cover property (A == '0 && C == '0);
  cover property (&A);                  // all ones applied
  cover property ($onehot(A));          // any single '1' exercised
  cover property (c_out[0]);            // final carry seen
  cover property (!c_out[0]);           // final carry not seen
endmodule

bind func5 func5_sva u_func5_sva(.clk(clk));


// Primitive FullAdder checker (optional but robust)
module FullAdder_sva(input logic clk);
  default clocking cb @(posedge clk); endclocking

  // Functional equivalence for every FA instance
  assert property (
    !$isunknown({a,b,c_in}) |->
    (sum == (a ^ b ^ c_in) &&
     c_out == ((a & b) | (c_in & (a ^ b))))
  );

  // Coverage: exercise both sum polarities and both carry outcomes
  cover property (sum);
  cover property (!sum);
  cover property (c_out);
  cover property (!c_out);
endmodule

bind FullAdder FullAdder_sva u_fa_sva(.clk(clk));