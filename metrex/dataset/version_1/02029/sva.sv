// SVA for comparator_4bit
module comparator_4bit_sva (
  input [3:0] A, B, C, D,
  input       eq, gt, lt
);
  default clocking cb @(A or B or C or D); endclocking
  default disable iff ($isunknown({A,B,C,D}));

  // Functional equivalence
  assert property (eq == ((A==B) && (B==C) && (C==D)));
  assert property (gt == ((A>B) && (B>C) && (C>D)));
  assert property (lt == ((A<B) && (B<C) && (C<D)));

  // Output sanity and mutual exclusion
  assert property (!$isunknown({eq,gt,lt}));
  assert property ($onehot0({eq,gt,lt}));

  // Coverage
  cover property (((A==B)&&(B==C)&&(C==D)) && eq);
  cover property (((A>B)&&(B>C)&&(C>D)) && gt);
  cover property (((A<B)&&(B<C)&&(C<D)) && lt);
  cover property (!eq && !gt && !lt);
endmodule

bind comparator_4bit comparator_4bit_sva u_comparator_4bit_sva (
  .A(A), .B(B), .C(C), .D(D), .eq(eq), .gt(gt), .lt(lt)
);