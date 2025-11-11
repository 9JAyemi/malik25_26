// SVA checker for base and wrapper_module
module xor_and_sva_checker (
  input logic A1, A2, B1, B2, X
);

  // Functional equivalence (use ##0 to avoid preponed sampling race)
  assert property (@(A1 or A2 or B1 or B2) ##0
    (X === ((A1 ^ A2) & (B1 ^ B2)))
  ) else $error("X != (A1^A2)&(B1^B2)");

  // Known-propagation: if inputs are known, X must be known
  assert property (@(A1 or A2 or B1 or B2) ##0
    (!$isunknown({A1,A2,B1,B2})) |-> !$isunknown(X)
  ) else $error("Known inputs produced unknown X");

  // Change correlation: X changes iff the ideal function changes
  assert property (@(A1 or A2 or B1 or B2) ##0
    ($changed(X) == $changed((A1 ^ A2) & (B1 ^ B2)))
  ) else $error("X change does not match functional change");

  // Functional coverage of XOR-term combinations
  cover property (@(A1 or A2 or B1 or B2) ##0 ((A1 ^ A2) && (B1 ^ B2)));
  cover property (@(A1 or A2 or B1 or B2) ##0 ((A1 ^ A2) && !(B1 ^ B2)));
  cover property (@(A1 or A2 or B1 or B2) ##0 (!(A1 ^ A2) && (B1 ^ B2)));
  cover property (@(A1 or A2 or B1 or B2) ##0 (!(A1 ^ A2) && !(B1 ^ B2)));

  // X toggle coverage
  cover property (@(A1 or A2 or B1 or B2) ##0 $rose(X));
  cover property (@(A1 or A2 or B1 or B2) ##0 $fell(X));

endmodule

// Bind to both modules (behavioral equivalence and connectivity)
bind base            xor_and_sva_checker base_chk     (.A1(A1), .A2(A2), .B1(B1), .B2(B2), .X(X));
bind wrapper_module  xor_and_sva_checker wrapper_chk  (.A1(A1), .A2(A2), .B1(B1), .B2(B2), .X(X));