// SVA checkers for the ripple-carry adder hierarchy.
// Bind these into the DUT; no DUT or TB changes required.

bind half_adder ha_sva ha_sva_i();
module ha_sva();
  // Scope has: A, B, S, C
  always_comb begin
    assert (S === (A ^ B)) else $error("half_adder: S != A^B");
    assert (C === (A & B)) else $error("half_adder: C != A&B");

    cover (A==0 && B==0);
    cover (A==0 && B==1);
    cover (A==1 && B==0);
    cover (A==1 && B==1);
  end
endmodule


bind full_adder fa_sva fa_sva_i();
module fa_sva();
  // Scope has: A, B, Cin, S, Cout, and internal s1, c1, c2
  always_comb begin
    // Functional equivalence
    assert (S    === (A ^ B ^ Cin)) else $error("full_adder: S != A^B^Cin");
    assert (Cout === ((A & B) | (Cin & (A ^ B)))) else $error("full_adder: Cout mismatch");

    // Structural consistency (internal nets)
    assert (s1 === (A ^ B)) else $error("full_adder: s1 != A^B");
    assert (c1 === (A & B)) else $error("full_adder: c1 != A&B");
    assert (c2 === (s1 & Cin)) else $error("full_adder: c2 != s1&Cin");
    assert (Cout === (c1 | c2)) else $error("full_adder: Cout != c1|c2");

    // Full input-space coverage (8 combos)
    cover ({A,B,Cin} == 3'b000);
    cover ({A,B,Cin} == 3'b001);
    cover ({A,B,Cin} == 3'b010);
    cover ({A,B,Cin} == 3'b011);
    cover ({A,B,Cin} == 3'b100);
    cover ({A,B,Cin} == 3'b101);
    cover ({A,B,Cin} == 3'b110);
    cover ({A,B,Cin} == 3'b111);

    // Carry observed both ways
    cover (Cout==0);
    cover (Cout==1);
  end
endmodule


bind r4_adder r4_sva r4_sva_i();
module r4_sva();
  // Scope has: A[3:0], B[3:0], Cin, S[3:0], Cout, c1,c2,c3 and instances fa1..fa4
  always_comb begin
    // Top-level functional check
    assert ({Cout, S} === (A + B + Cin)) else $error("r4_adder: {Cout,S} != A+B+Cin");

    // Bit-wise carry chain checks
    assert ({c1, S[0]} === (A[0] + B[0] + Cin)) else $error("r4_adder: bit0 sum/carry mismatch");
    assert ({c2, S[1]} === (A[1] + B[1] + c1 )) else $error("r4_adder: bit1 sum/carry mismatch");
    assert ({c3, S[2]} === (A[2] + B[2] + c2 )) else $error("r4_adder: bit2 sum/carry mismatch");
    assert ({Cout,S[3]} === (A[3] + B[3] + c3)) else $error("r4_adder: bit3 sum/carry mismatch");

    // Connectivity to sub-instances (defensive)
    assert (fa2.Cin === c1) else $error("r4_adder: fa2 Cin not driven by c1");
    assert (fa3.Cin === c2) else $error("r4_adder: fa3 Cin not driven by c2");
    assert (fa4.Cin === c3) else $error("r4_adder: fa4 Cin not driven by c3");

    // Coverage: no-carry, ripple-through, overflow
    cover (!c1 && !c2 && !c3 && !Cout); // no carries
    cover ( c1 &&  c2 &&  c3          ); // ripple through lower 3 bits
    cover ( Cout );                      // overflow out of bit3
    // Exercise mixed patterns
    cover ( c1 && !c2 ); 
    cover (!c1 &&  c2 );
  end
endmodule


bind r16_adder r16_sva r16_sva_i();
module r16_sva();
  // Scope has: A[15:0], B[15:0], Cin, S[15:0], Cout, c1,c2,c3 and instances a1..a4
  always_comb begin
    // Top-level functional check
    assert ({Cout, S} === (A + B + Cin)) else $error("r16_adder: {Cout,S} != A+B+Cin");

    // Nibble-wise carry chain checks
    assert ({c1,   S[ 3: 0]} === (A[ 3: 0] + B[ 3: 0] + Cin)) else $error("r16_adder: nibble0 mismatch");
    assert ({c2,   S[ 7: 4]} === (A[ 7: 4] + B[ 7: 4] + c1 )) else $error("r16_adder: nibble1 mismatch");
    assert ({c3,   S[11: 8]} === (A[11: 8] + B[11: 8] + c2 )) else $error("r16_adder: nibble2 mismatch");
    assert ({Cout, S[15:12]} === (A[15:12] + B[15:12] + c3 )) else $error("r16_adder: nibble3 mismatch");

    // Connectivity across r4 blocks
    assert (a2.Cin === c1) else $error("r16_adder: a2 Cin not driven by c1");
    assert (a3.Cin === c2) else $error("r16_adder: a3 Cin not driven by c2");
    assert (a4.Cin === c3) else $error("r16_adder: a4 Cin not driven by c3");

    // Coverage: boundary scenarios
    cover (A==16'h0000 && B==16'h0000 && Cin==0 && S==16'h0000 && Cout==0); // all zeros
    cover (A==16'hFFFF && B==16'h0000 && Cin==1 && S==16'h0000 && Cout==1); // full ripple propagate
    cover (A==16'hFFFF && B==16'hFFFF && Cin==1 && Cout==1);                // overflow max + max + 1
    cover (!c1 && !c2 && !c3 && !Cout);                                     // no carries
    cover ( c1 &&  c2 &&  c3 &&  Cout);                                     // carries through all nibbles
  end
endmodule