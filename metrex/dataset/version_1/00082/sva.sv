// SVA bind file for add8 hierarchy. Focused, concise checks and coverage.

bind full_adder
module full_adder_sva;
  // Combinational correctness and X/Z guard
  always_comb begin
    assert (!$isunknown({A,B,Cin})) else $error("full_adder: X/Z on inputs");
    assert ({Cout,S} == A + B + Cin) else $error("full_adder: sum/carry mismatch");
    if ((A ^ B) && !(A & B)) begin
      assert (Cout == Cin && S == ~Cin) else $error("full_adder: propagate case wrong");
    end
  end
  // Lightweight functional coverage
  always_comb begin
    cover (A==0 && B==0 && Cin==0);        // zero add
    cover ((A&B)==1'b1);                   // generate
    cover ((A^B)==1'b1 && (A&B)==1'b0);    // propagate
    cover (~A && ~B);                      // kill
  end
endmodule


bind adder_4bit
module adder4_sva;
  // End-to-end arithmetic and input sanity
  always_comb begin
    assert (!$isunknown({A,B,Cin})) else $error("adder_4bit: X/Z on inputs");
    assert ({Cout,S} == A + B + Cin) else $error("adder_4bit: wrong 4-bit sum");
  end
  // Carry-chain connectivity inside the ripple
  always_comb begin
    assert (inst1.Cout === C[0]) else $error("adder_4bit: C[0] mismatch");
    assert (inst2.Cin  === C[0]) else $error("adder_4bit: inst2 Cin not C[0]");
    assert (inst2.Cout === C[1]) else $error("adder_4bit: C[1] mismatch");
    assert (inst3.Cin  === C[1]) else $error("adder_4bit: inst3 Cin not C[1]");
    assert (inst3.Cout === C[2]) else $error("adder_4bit: C[2] mismatch");
    assert (inst4.Cin  === C[2]) else $error("adder_4bit: inst4 Cin not C[2]");
  end
  // Coverage: exercise carries and extremes
  always_comb begin
    cover ((A+B+Cin) > 15);        // overflow carry-out
    cover ((A+B+Cin) == 0);        // zero result
    cover (C[0]); cover (C[1]); cover (C[2]); // internal carries seen
    cover (A==4'hF && B==4'hF && Cin==1'b0);
  end
endmodule


bind add8
module add8_sva;
  // Top-level arithmetic and X/Z guard
  always_comb begin
    assert (!$isunknown({X,Y})) else $error("add8: X/Z on inputs");
    assert ({Cout,S} == X + Y) else $error("add8: wrong 8-bit sum");
  end
  // Structural carry chaining and nibble-level correctness
  always_comb begin
    assert (inst1.Cout === inst2.Cin) else $error("add8: carry between nibbles broken");
    assert (inst1.Cin  === 1'b0) else $error("add8: low nibble Cin must be tied to 0");
    assert ({inst1.Cout, S[3:0]} == X[3:0] + Y[3:0]) else $error("add8: low nibble wrong");
    assert ({Cout,      S[7:4]} == X[7:4] + Y[7:4] + inst1.Cout) else $error("add8: high nibble wrong");
  end
  // Coverage: edge and overflow scenarios
  always_comb begin
    cover (X==8'h00 && Y==8'h00);     // zero add
    cover (X==8'hFF && Y==8'h01);     // overflow
    cover (Cout);                     // top-level carry observed
    cover (inst1.Cout);               // carry from low nibble observed
  end
endmodule