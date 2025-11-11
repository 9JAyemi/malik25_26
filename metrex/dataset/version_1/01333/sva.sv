// SVA for and3_not_A
// Bind-friendly checker with internal nets
module and3_not_A_sva (
  input logic A,
  input logic B,
  input logic C,
  input logic X,
  input logic not_A,
  input logic and_B_C
);
  // Functional correctness and X-propagation guarded by known inputs
  always_comb begin
    if (!$isunknown({A,B,C})) begin
      assert #0 (not_A == ~A) else $error("not_A != ~A");
      assert #0 (and_B_C == (B & C)) else $error("and_B_C != (B & C)");
      assert #0 (X == ((~A) & B & C)) else $error("X != (~A & B & C)");
      assert #0 (!$isunknown({not_A,and_B_C,X})) else $error("X or internal went X/Z with known inputs");
    end
  end

  // Minimal but complete functional coverage
  always_comb begin
    // All input minterms
    cover ({A,B,C} == 3'b000);
    cover ({A,B,C} == 3'b001);
    cover ({A,B,C} == 3'b010);
    cover ({A,B,C} == 3'b011);
    cover ({A,B,C} == 3'b100);
    cover ({A,B,C} == 3'b101);
    cover ({A,B,C} == 3'b110);
    cover ({A,B,C} == 3'b111);
    // Output outcomes
    cover (X == 1'b0);
    cover (X == 1'b1);
    // Assertion condition hit (the only 1 case)
    cover (!A && B && C && X);
  end
endmodule

// Bind this checker to the DUT (accessing internal nets)
bind and3_not_A and3_not_A_sva u_and3_not_A_sva (
  .A(A),
  .B(B),
  .C(C),
  .X(X),
  .not_A(not_A),
  .and_B_C(and_B_C)
);