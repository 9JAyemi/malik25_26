// SVA for bitwise_operators: final behavior is result == ~num1 (num2 is ignored)
// Bind this to the DUT instance:
// bind bitwise_operators bitwise_operators_sva #(.n(n)) u_bitwise_operators_sva (.*);

module bitwise_operators_sva #(parameter int n = 8) (
  input logic [n-1:0] num1,
  input logic [n-1:0] num2,
  input logic [n-1:0] result
);

  // Functional correctness: result is always bitwise NOT of num1
  property p_func;
    @(*) (result === ~num1);
  endproperty
  ap_func: assert property (p_func)
    else $error("result must be ~num1");

  // Zero-delay combinational update when num1 changes
  property p_zero_delay;
    @(*) $changed(num1) |-> ##0 (result === ~num1);
  endproperty
  ap_zero_delay: assert property (p_zero_delay)
    else $error("result not updated combinationally from num1");

  // result must not change unless num1 changes (num2 must not affect result)
  property p_depends_only_on_num1;
    @(*) $changed(result) |-> $changed(num1);
  endproperty
  ap_depends_only_on_num1: assert property (p_depends_only_on_num1)
    else $error("result changed without num1 changing");

  // Explicitly prove num2 has no effect when num1 is stable
  property p_num2_no_effect;
    @(*) $stable(num1) && $changed(num2) |-> ##0 $stable(result);
  endproperty
  ap_num2_no_effect: assert property (p_num2_no_effect)
    else $error("num2 affected result while num1 was stable");

  // When num1 is fully known, result must be fully known (no X/Z leakage)
  property p_known_propagation;
    @(*) !$isunknown(num1) |-> !$isunknown(result);
  endproperty
  ap_known_propagation: assert property (p_known_propagation)
    else $error("result has X/Z while num1 is known");

  // Coverage: observe that each bit inversion behavior occurs in both directions
  genvar i;
  generate
    for (i = 0; i < n; i++) begin : cov_bits
      // num1[i]: 0->1 should cause result[i]: 1->0 in same delta
      cp_bit01: cover property (@(*) !$isunknown(num1[i]) && $rose(num1[i]) ##0 $fell(result[i]));
      // num1[i]: 1->0 should cause result[i]: 0->1 in same delta
      cp_bit10: cover property (@(*) !$isunknown(num1[i]) && $fell(num1[i]) ##0 $rose(result[i]));
    end
  endgenerate

  // Coverage: extremes and num2 activity while num1 stable
  cp_all_zero: cover property (@(*) result == '0);
  cp_all_ones: cover property (@(*) result == '1);
  cp_num2_tog_stable_num1: cover property (@(*) $stable(num1) && $changed(num2));

endmodule