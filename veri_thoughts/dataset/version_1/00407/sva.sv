// SVA for math_operation: result = (a + 2*b) mod 16
module math_operation_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [3:0] result
);

  // No X/Z allowed on inputs or output
  assert property (@(a or b or result) ##0 !$isunknown({a,b,result}))
    else $error("X/Z detected on a/b/result");

  // Functional equivalence (use ##0 to avoid race with continuous assign)
  assert property (@(a or b or result) ##0 (result === ((a + (b<<1)) & 4'hF)))
    else $error("Functional mismatch: result != (a + 2*b) mod 16");

  // Useful bit-level invariant: doubling b is even, so LSB must match a[0]
  assert property (@(a or b or result) ##0 (result[0] == a[0]))
    else $error("LSB mismatch: result[0] must equal a[0]");

  // Coverage: hit all possible result values
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : cov_res_vals
      cover property (@(a or b or result) ##0 (result == v[3:0]));
    end
  endgenerate

  // Coverage: key corner cases and overflow/wrap
  cover property (@(a or b) ##0 (a==4'h0 && b==4'h0));     // zero + zero
  cover property (@(a or b) ##0 (a==4'hF && b==4'hF));     // max + max*2 (wrap very likely)
  cover property (@(a or b) ##0 ((a + (b<<1)) > 4'hF));    // overflow/wrap occurs
  cover property (@(a or b) ##0 (a==4'h0));                // pure double of b
  cover property (@(a or b) ##0 (b==4'h0));                // pass-through a
endmodule

// Bind into DUT
bind math_operation math_operation_sva sva_inst (.a(a), .b(b), .result(result));