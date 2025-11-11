// SVA for multiplier. Bind this to the DUT.
// Focus: functional correctness, X-propagation, and basic combinational sanity.

module multiplier_sva (
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [15:0] result
);

  // When inputs change, check in the same time (##0) that result matches a*b
  // and that no X/Z propagate if inputs are clean.
  property p_correct_unsigned_product;
    @(a or b) !$isunknown({a,b}) |-> ##0 (result == (a * b));
  endproperty
  assert property (p_correct_unsigned_product);

  property p_known_in_implies_known_out;
    @(a or b) !$isunknown({a,b}) |-> ##0 !$isunknown(result);
  endproperty
  assert property (p_known_in_implies_known_out);

  // Result should only change when inputs change (combinational, no latches).
  property p_result_changes_only_with_inputs;
    @(a or b or result) $changed(result) |-> ($changed(a) || $changed(b));
  endproperty
  assert property (p_result_changes_only_with_inputs);

  // Basic algebraic identities (redundant with main check but good for debug).
  assert property (@(a or b) (a==8'd0 || b==8'd0) |-> ##0 (result==16'd0));
  assert property (@(a or b) (a==8'd1)             |-> ##0 (result=={8'd0,b}));
  assert property (@(a or b) (b==8'd1)             |-> ##0 (result=={8'd0,a}));

  // Coverage: hit zeros, ones, max, and cases with non-zero upper product bits.
  cover property (@(a or b) ##0 (a==8'd0 && b==8'd0));
  cover property (@(a or b) ##0 (a==8'd1));
  cover property (@(a or b) ##0 (b==8'd1));
  cover property (@(a or b) ##0 (a==8'hFF && b==8'hFF));
  cover property (@(a or b) ##0 (result[15:8] != 8'd0)); // exercises high bits
  // Exercise single-bit a with arbitrary b (helps catch shift/width issues)
  genvar k;
  generate
    for (k=0; k<8; k++) begin : g_onehot_cov
      cover property (@(a or b) ##0 (a == (8'b1 << k)));
    end
  endgenerate

endmodule

// Bind to the DUT
bind multiplier multiplier_sva u_multiplier_sva (.a(a), .b(b), .result(result));