// SVA for comparator: checks functional correctness and covers key cases.
// Bind this to the DUT.

module comparator_sva (
  input logic [15:0] A,
  input logic [15:0] B,
  input logic        result
);

  // Output must never be X/Z
  a_no_x: assert property (@(A or B or result) ##0 !$isunknown(result))
    else $error("comparator: result is X/Z");

  // Functional equivalence (guard against X/Z on inputs); use ##0 to avoid race
  a_func: assert property (@(A or B) (!$isunknown({A,B})) |-> ##0 (result === (A <= B)))
    else $error("comparator: mismatch A=%0d B=%0d result=%0b exp=%0b", A, B, result, (A<=B));

  // Functional coverage of all relation outcomes
  c_lt: cover property (@(A or B) (!$isunknown({A,B})) && (A <  B) ##0 result);
  c_eq: cover property (@(A or B) (!$isunknown({A,B})) && (A == B) ##0 result);
  c_gt: cover property (@(A or B) (!$isunknown({A,B})) && (A >  B) ##0 !result);

  // Corner-case coverage
  c_minmin: cover property (@(A or B) (A==16'h0000 && B==16'h0000) ##0 result);
  c_maxmax: cover property (@(A or B) (A==16'hFFFF && B==16'hFFFF) ##0 result);
  c_minmax: cover property (@(A or B) (A==16'h0000 && B==16'hFFFF) ##0 result);
  c_maxmin: cover property (@(A or B) (A==16'hFFFF && B==16'h0000) ##0 !result);

endmodule

bind comparator comparator_sva u_comparator_sva (.A(A), .B(B), .result(result));