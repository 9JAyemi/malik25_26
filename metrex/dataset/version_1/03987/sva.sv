// SVA for xor_reset
module xor_reset_sva (
    input logic in1,
    input logic in2,
    input logic reset,
    input logic out1
);
  // Sample on any change; use ##0 to observe post-NBA values
  default clocking cb @(in1 or in2 or reset); endclocking

  // Functional equivalence
  property p_func; 1'b1 |-> ##0 (out1 === (reset ? 1'b0 : (in1 ^ in2))); endproperty
  a_func: assert property (p_func)
    else $error("xor_reset: out1 != (reset ? 0 : in1^in2)");

  // Known-value check (no X/Z) when reset=1 or when reset=0 and inputs are known
  a_known: assert property (
      (((reset === 1'b1)) || ((reset === 1'b0) && !$isunknown({in1,in2}))))
      |-> ##0 (!$isunknown(out1))
  ) else $error("xor_reset: out1 is X/Z under defined conditions");

  // Coverage: reset behavior and full XOR truth table under reset=0
  c_reset:  cover property (reset ##0 (out1 == 1'b0));
  c_00:     cover property ((!reset && (in1==1'b0) && (in2==1'b0)) ##0 (out1==1'b0));
  c_01:     cover property ((!reset && (in1==1'b0) && (in2==1'b1)) ##0 (out1==1'b1));
  c_10:     cover property ((!reset && (in1==1'b1) && (in2==1'b0)) ##0 (out1==1'b1));
  c_11:     cover property ((!reset && (in1==1'b1) && (in2==1'b1)) ##0 (out1==1'b0));
endmodule

// Bind into DUT
bind xor_reset xor_reset_sva u_xor_reset_sva(.in1(in1), .in2(in2), .reset(reset), .out1(out1));