// SVA checker for three_to_one (3-input majority)
module three_to_one_sva (input logic A, B, C, X);

  // Combinational correctness (with race-free sampling)
  always_comb begin
    // Known-value check
    assert (#0 !($isunknown({A,B,C,X})))
      else $error("three_to_one: X/Z detected A=%b B=%b C=%b X=%b", A,B,C,X);

    // Functional majority check
    assert (#0 X === ($countones({A,B,C}) >= 2))
      else $error("three_to_one: mismatch A=%0b B=%0b C=%0b X=%0b", A,B,C,X);

    // Full truth-table coverage (and correct X)
    cover (({A,B,C}==3'b000) && (X==0));
    cover (({A,B,C}==3'b001) && (X==0));
    cover (({A,B,C}==3'b010) && (X==0));
    cover (({A,B,C}==3'b100) && (X==0));
    cover (({A,B,C}==3'b011) && (X==1));
    cover (({A,B,C}==3'b101) && (X==1));
    cover (({A,B,C}==3'b110) && (X==1));
    cover (({A,B,C}==3'b111) && (X==1));
  end

  // Redundant algebraic form (concise equivalence)
  assert property ( X == ((A & B) | (A & C) | (B & C)) );

  // Minimal toggle coverage on X
  cover property ( $changed(X) );

endmodule

// Bind into DUT
bind three_to_one three_to_one_sva u_three_to_one_sva (.A(A), .B(B), .C(C), .X(X));