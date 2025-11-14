// SVA checker for four_to_one
module four_to_one_sva (
  input logic A1, A2, B1, B2,
  input logic Y
);

  // Functional equivalence when all inputs are known
  assert property (@(*)
    (!$isunknown({A1,A2,B1,B2})) |->
      (Y == ((A1 & A2) ? B1 : ((A1 ^ A2) ? B2 : (B1 & B2))))
  );

  // Output must be known when inputs are known
  assert property (@(*)
    (!$isunknown({A1,A2,B1,B2})) |-> !$isunknown(Y)
  );

  // Branch-specific correctness (with data-known guards)
  assert property (@(*)
    ((A1 & A2) && !$isunknown(B1)) |-> (Y == B1)
  );
  assert property (@(*)
    ((A1 ^ A2) && !$isunknown(B2)) |-> (Y == B2)
  );
  assert property (@(*)
    ((~A1 & ~A2) && !$isunknown({B1,B2})) |-> (Y == (B1 & B2))
  );

  // Select-line coverage/exclusivity (when A inputs known)
  assert property (@(*)
    (!$isunknown({A1,A2})) |-> $onehot({(A1 & A2), (A1 ^ A2), (~A1 & ~A2)})
  );

  // Coverage: exercise each branch producing both Y=0 and Y=1
  cover property (@(*) (A1 & A2) && (B1==0) && (Y==0));
  cover property (@(*) (A1 & A2) && (B1==1) && (Y==1));

  cover property (@(*) (A1 ^ A2) && (B2==0) && (Y==0));
  cover property (@(*) (A1 ^ A2) && (B2==1) && (Y==1));

  cover property (@(*) (~A1 & ~A2) && (B1==0) && (B2==0) && (Y==0));
  cover property (@(*) (~A1 & ~A2) && (B1==1) && (B2==1) && (Y==1));

endmodule

// Bind into DUT
bind four_to_one four_to_one_sva sva_i (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .Y(Y)
);