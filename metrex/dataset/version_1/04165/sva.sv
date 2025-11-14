// SVA for multiplier (8x8 signed -> 16-bit signed)
module multiplier_sva (
  input  signed [7:0]  A,
  input  signed [7:0]  B,
  input  signed [15:0] C
);

  // Core functional check (zero-latency combinational correctness)
  property p_correct_same_cycle;
    @(A or B) !$isunknown({A,B}) |-> ##0 (C === $signed(A) * $signed(B));
  endproperty
  assert property (p_correct_same_cycle);

  // No X/Z on output when inputs are known
  property p_defined_output;
    @(A or B) !$isunknown({A,B}) |-> !$isunknown(C);
  endproperty
  assert property (p_defined_output);

  // Stability: if inputs don't change, output must not change
  property p_stable_when_inputs_stable;
    @(A or B or C) $stable({A,B}) |-> $stable(C);
  endproperty
  assert property (p_stable_when_inputs_stable);

  // Coverage: sign combinations and special values
  localparam signed [7:0] MIN8 = -128;
  localparam signed [7:0] MAX8 =  127;

  cover property (@(A or B) !$isunknown({A,B}) && ($signed(A) > 0 && $signed(B) > 0));
  cover property (@(A or B) !$isunknown({A,B}) && ($signed(A) < 0 && $signed(B) < 0));
  cover property (@(A or B) !$isunknown({A,B}) && (($signed(A) > 0 && $signed(B) < 0) || ($signed(A) < 0 && $signed(B) > 0)));
  cover property (@(A or B) !$isunknown({A,B}) && (A == 0 || B == 0));
  cover property (@(A or B) !$isunknown({A,B}) && (A == 1 || B == 1));
  cover property (@(A or B) !$isunknown({A,B}) && (A == -1 || B == -1));
  cover property (@(A or B) !$isunknown({A,B}) && (A == MIN8));
  cover property (@(A or B) !$isunknown({A,B}) && (B == MIN8));
  cover property (@(A or B) !$isunknown({A,B}) && (A == MAX8));
  cover property (@(A or B) !$isunknown({A,B}) && (B == MAX8));

  // Corner products
  cover property (@(A or B) !$isunknown({A,B}) && (A == MAX8 && B == MAX8)); // 127*127
  cover property (@(A or B) !$isunknown({A,B}) && (A == MIN8 && B == MIN8)); // -128*-128
  cover property (@(A or B) !$isunknown({A,B}) && ((A == MIN8 && B == MAX8) || (A == MAX8 && B == MIN8)));

  // Change patterns (A only, B only, both)
  cover property (@(A or B) !$isunknown({A,B}) && $changed(A) && !$changed(B));
  cover property (@(A or B) !$isunknown({A,B}) && !$changed(A) && $changed(B));
  cover property (@(A or B) !$isunknown({A,B}) && $changed(A) && $changed(B));

endmodule

// Bind SVA to the DUT
bind multiplier multiplier_sva m_mult_sva (.A(A), .B(B), .C(C));