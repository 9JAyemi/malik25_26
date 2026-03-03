// SVA checker for adder4bit_carry (combinational)
// Bind into the DUT for automatic checking
module adder4bit_carry_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       cin,
  input  logic [3:0] S,
  input  logic       cout
);

  // X/Z sanity: if inputs are clean, outputs must be clean
  always_comb begin
    assert (!$isunknown({A,B,cin})) else $error("adder4bit_carry: X/Z on inputs A/B/cin");
    if (!$isunknown({A,B,cin})) begin
      assert (!$isunknown({S,cout})) else $error("adder4bit_carry: X/Z on outputs S/cout with clean inputs");
    end
  end

  // Functional equivalence (zero-extended addition)
  always_comb begin
    assert (#0 {cout,S} == ({1'b0,A} + {1'b0,B} + {1'b0,cin}))
      else $error("adder4bit_carry mismatch: A=%0h B=%0h cin=%0b -> S=%0h cout=%0b", A, B, cin, S, cout);
  end

  // Concise coverage to exercise key corners
  always_comb begin
    cover ({cout,S} == 5'd0);              // 0+0+0
    cover (cin == 1'b0);                   // cin low seen
    cover (cin == 1'b1);                   // cin high seen
    cover (cout == 1'b0 && S == 4'hF);     // boundary no-carry max (15)
    cover (cout == 1'b1 && S == 4'h0);     // wrap with carry (sum=16)
    cover ({cout,S} == 5'd31);             // top end (sum=31)
  end

endmodule

// Bind the checker to the DUT
bind adder4bit_carry adder4bit_carry_sva u_adder4bit_carry_sva (
  .A(A), .B(B), .cin(cin), .S(S), .cout(cout)
);