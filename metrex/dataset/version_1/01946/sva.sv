// SVA for HalfSubtractor and FullSubtractor
// Concise, functionally complete, with targeted coverage

// HalfSubtractor checker
module HalfSubtractor_sva(input logic A, B, difference, borrow);
  // No X/Zs
  assert property (@(*)
    !$isunknown({A,B,difference,borrow})
  );

  // Functional equivalence
  assert property (@(*)
    difference == (A ^ B)
  );
  assert property (@(*)
    borrow == (~A & B)
  );

  // Truth-table coverage (all 4 minterms with expected outputs)
  cover property (@(*)
    (!A && !B && !difference && !borrow)
  );
  cover property (@(*)
    (!A &&  B &&  difference &&  borrow)
  );
  cover property (@(*)
    ( A && !B &&  difference && !borrow)
  );
  cover property (@(*)
    ( A &&  B && !difference && !borrow)
  );
endmodule

bind HalfSubtractor HalfSubtractor_sva hs_chk(.A(A), .B(B), .difference(difference), .borrow(borrow));


// FullSubtractor checker
module FullSubtractor_sva(
  input  logic A, B, borrow, difference, borrow_out,
  input  logic temp_diff1, temp_borrow1, temp_borrow2
);
  // No X/Zs anywhere (incl. internal nets)
  assert property (@(*)
    !$isunknown({A,B,borrow,difference,borrow_out,temp_diff1,temp_borrow1,temp_borrow2})
  );

  // Stage-wise correctness (verifies both HalfSubtractor instances)
  assert property (@(*)
    temp_diff1    == (A ^ B)
  );
  assert property (@(*)
    temp_borrow1  == (~A & B)
  );
  assert property (@(*)
    difference    == (temp_diff1 ^ borrow)
  );
  assert property (@(*)
    temp_borrow2  == (~temp_diff1 & borrow)
  );
  assert property (@(*)
    borrow_out    == (temp_borrow1 | temp_borrow2)
  );

  // Canonical functional checks
  assert property (@(*)
    difference == (A ^ B ^ borrow)
  );
  assert property (@(*)
    borrow_out == ((~A & B) | (~(A ^ B) & borrow))
  );

  // Borrow cannot originate from both stages simultaneously
  assert property (@(*)
    !(temp_borrow1 && temp_borrow2)
  );

  // Input-space coverage (all 8 minterms)
  cover property (@(*) (!A && !B && !borrow)); // 0,0,0
  cover property (@(*) (!A && !B &&  borrow)); // 0,0,1
  cover property (@(*) (!A &&  B && !borrow)); // 0,1,0
  cover property (@(*) (!A &&  B &&  borrow)); // 0,1,1
  cover property (@(*) ( A && !B && !borrow)); // 1,0,0
  cover property (@(*) ( A && !B &&  borrow)); // 1,0,1
  cover property (@(*) ( A &&  B && !borrow)); // 1,1,0
  cover property (@(*) ( A &&  B &&  borrow)); // 1,1,1

  // Coverage: borrow source per stage
  cover property (@(*) ( temp_borrow1 && !temp_borrow2)); // from stage1
  cover property (@(*) (!temp_borrow1 &&  temp_borrow2)); // from stage2
endmodule

bind FullSubtractor FullSubtractor_sva fs_chk(
  .A(A), .B(B), .borrow(borrow), .difference(difference), .borrow_out(borrow_out),
  .temp_diff1(temp_diff1), .temp_borrow1(temp_borrow1), .temp_borrow2(temp_borrow2)
);