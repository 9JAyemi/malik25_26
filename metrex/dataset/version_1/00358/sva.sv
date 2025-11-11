// SVA for magnitude_comparator
// Concise, full-check equivalence to signed >=, with key partition coverage.

module magnitude_comparator_sva (
  input  logic [3:0] in_1,
  input  logic [3:0] in_0,
  input  logic       greater_than_or_equal
);

  // Output must be known when inputs are known
  assert property (@(*) (!$isunknown({in_1,in_0})) |-> !$isunknown(greater_than_or_equal))
    else $error("gte X/Z with known inputs");

  // Golden functional equivalence: signed comparison
  assert property (@(*) (!$isunknown({in_1,in_0})) |-> 
                   (greater_than_or_equal == ($signed(in_1) >= $signed(in_0))))
    else $error("gte != signed(in_1) >= signed(in_0)");

  // Explicit sign-different branch check (debug-friendly)
  assert property (@(*) (!$isunknown({in_1,in_0})) && (in_1[3] != in_0[3]) |-> 
                   (greater_than_or_equal == (in_1[3] == 1'b0)))
    else $error("gte sign-branch wrong");

  // Functional partition coverage
  cover property (@(*) (!$isunknown({in_1,in_0})) && (in_1 == in_0) && greater_than_or_equal);
  cover property (@(*) (!$isunknown({in_1,in_0})) && (in_1[3] != in_0[3]) && (in_1[3]==1'b0) &&  greater_than_or_equal);
  cover property (@(*) (!$isunknown({in_1,in_0})) && (in_1[3] != in_0[3]) && (in_1[3]==1'b1) && !greater_than_or_equal);
  cover property (@(*) (!$isunknown({in_1,in_0})) && (in_1[3] == in_0[3]) && (in_1 >  in_0) &&  greater_than_or_equal);
  cover property (@(*) (!$isunknown({in_1,in_0})) && (in_1[3] == in_0[3]) && (in_1 <  in_0) && !greater_than_or_equal);

  // Boundary/sign-extreme covers
  cover property (@(*) (in_1 == 4'sh7) && (in_0 == 4'sh8) &&  greater_than_or_equal); // +7 >= -8
  cover property (@(*) (in_1 == 4'sh8) && (in_0 == 4'sh7) && !greater_than_or_equal); // -8 >= +7 -> 0

endmodule

bind magnitude_comparator magnitude_comparator_sva sva_mc (
  .in_1(in_1),
  .in_0(in_0),
  .greater_than_or_equal(greater_than_or_equal)
);