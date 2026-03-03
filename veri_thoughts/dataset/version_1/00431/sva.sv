// SVA for adder16: concise, high-quality checks and targeted coverage.
// Bind these assertions to the DUT.

module adder16_sva #(parameter W=16)
(
  input logic [W-1:0] A,
  input logic [W-1:0] B,
  input logic [W-1:0] Y
);
  localparam logic [W-1:0] MASK = {W{1'b1}};

  // Functional equivalence (4-state tolerant): Y matches A+B bit-for-bit (including X/Z)
  assert property (Y === (A + B))
    else $error("adder16: Y != A+B (4-state mismatch)");

  // Known-on-known: with fully known inputs, output must be fully known and correct
  assert property (!$isunknown({A,B}) |-> (!$isunknown(Y) && (Y == (A + B))))
    else $error("adder16: known inputs did not produce known/correct output");

  // Identity: adding zero returns the other operand (when inputs known)
  assert property (!$isunknown({A,B}) && (A==0) |-> (Y==B))
    else $error("adder16: A==0 but Y!=B");

  assert property (!$isunknown({A,B}) && (B==0) |-> (Y==A))
    else $error("adder16: B==0 but Y!=A");

  // Algebraic inverses modulo 2^W (when values are known)
  assert property (!$isunknown({A,B,Y}) |->
                   (((Y - B) & MASK) == A && ((Y - A) & MASK) == B))
    else $error("adder16: modulo-2^W inverse check failed");

  // Coverage: key corner cases and behaviors
  cover property (!$isunknown({A,B}) && ({1'b0,A}+{1'b0,B})[W]);                // carry/overflow occurred
  cover property (!$isunknown({A,B}) && !({1'b0,A}+{1'b0,B})[W]);               // no carry
  cover property (A=={W{1'b0}} && B=={W{1'b0}} && Y=={W{1'b0}});                // 0+0 -> 0
  cover property (A=={W{1'b1}} && B=={{(W-1){1'b0}},1'b1} && Y=={W{1'b0}});     // 0xFFFF + 1 -> wrap to 0
  cover property (A=={W{1'b1}} && B=={W{1'b1}} && Y==({W{1'b1}} - 1));          // max+max -> 0xFFFE
  cover property (A==({1'b1, {W-1{1'b0}}}) && B==({1'b1, {W-1{1'b0}}}));        // 0x8000 + 0x8000 (carry into MSB)
endmodule

// Bind to all instances of adder16
bind adder16 adder16_sva #(.W(16)) adder16_sva_i (.A(A), .B(B), .Y(Y));