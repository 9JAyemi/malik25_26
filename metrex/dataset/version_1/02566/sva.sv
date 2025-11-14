// SVA binders/checkers for full_adder and ripple_carry_adder

// Full-adder checker
module full_adder_sva (
  input logic A, B, C_in, S, C_out
);
  // Functional equivalence and X-propagation checks
  always_comb begin
    #0 assert ({C_out,S} === A + B + C_in)
      else $error("full_adder mismatch: A=%0b B=%0b Cin=%0b -> S=%0b Cout=%0b",
                  A,B,C_in,S,C_out);

    if (!$isunknown({A,B,C_in}))
      assert (!$isunknown({S,C_out}))
        else $error("full_adder produced X/Z on outputs for known inputs");
  end

  // Input space coverage (all 8 combinations)
  always_comb begin
    cover ({A,B,C_in} == 3'b000);
    cover ({A,B,C_in} == 3'b001);
    cover ({A,B,C_in} == 3'b010);
    cover ({A,B,C_in} == 3'b011);
    cover ({A,B,C_in} == 3'b100);
    cover ({A,B,C_in} == 3'b101);
    cover ({A,B,C_in} == 3'b110);
    cover ({A,B,C_in} == 3'b111);
  end
endmodule

bind full_adder full_adder_sva fa_chk (.*);

// Ripple-carry adder checker
module ripple_carry_adder_sva #(
  parameter int n = 4
) (
  input  logic [n-1:0] A,
  input  logic [n-1:0] B,
  input  logic [n:0]   C
);
  logic [n:0] exp;
  assign exp = {1'b0, A} + {1'b0, B};

  always_comb begin
    #0 assert (C === exp)
      else $error("rca mismatch: A=0x%0h B=0x%0h C=0x%0h exp=0x%0h", A, B, C, exp);

    if (!$isunknown({A,B}))
      assert (!$isunknown(C))
        else $error("rca produced X/Z on C for known inputs");

    // LSB sum must be XOR when Cin=0
    assert (C[0] === (A[0] ^ B[0]))
      else $error("rca LSB sum mismatch (Cin=0): A0=%0b B0=%0b C0=%0b", A[0], B[0], C[0]);
  end

  // Corner-case coverage
  always_comb begin
    cover (A == '0  && B == '0 );  // zero + zero
    cover (A == '0  && B == '1 );  // zero + all-ones
    cover (A == '1  && B == '0 );  // all-ones + zero
    cover (A == '1  && B == '1 );  // full ripple (all generates)
    cover (A == ~B);               // full propagate
    cover (C[n] == 1'b1);          // overflow seen
    cover (C[n] == 1'b0);          // no overflow seen
  end
endmodule

bind ripple_carry_adder ripple_carry_adder_sva #(.n(n)) rca_chk (.*);