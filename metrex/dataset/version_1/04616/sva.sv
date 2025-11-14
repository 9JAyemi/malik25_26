// SVA for ripple_adder_4bit and full_adder
// Bind checkers; concise, high-quality functional and structural checks plus targeted coverage.
`ifndef SYNTHESIS

checker ripple_adder_4bit_sva;

  // Recompute expected carries and sums
  logic c0, c1, c2, c3;
  logic [3:0] expS;
  logic       expCout;
  logic       known_in;

  always_comb begin
    known_in = !$isunknown({A,B,Cin});

    c0 = (A[0]&B[0]) | (A[0]&Cin) | (B[0]&Cin);
    expS[0] = A[0]^B[0]^Cin;

    c1 = (A[1]&B[1]) | (A[1]&c0)  | (B[1]&c0);
    expS[1] = A[1]^B[1]^c0;

    c2 = (A[2]&B[2]) | (A[2]&c1)  | (B[2]&c1);
    expS[2] = A[2]^B[2]^c1;

    c3 = (A[3]&B[3]) | (A[3]&c2)  | (B[3]&c2);
    expS[3] = A[3]^B[3]^c2;

    expCout = c3;

    if (known_in) begin
      // End-to-end equivalence
      assert ({Cout,S} == {expCout,expS})
        else $error("Ripple adder mismatch: A=%0h B=%0h Cin=%0b -> S=%0h Cout=%0b, exp S=%0h Cout=%0b",
                    A, B, Cin, S, Cout, expS, expCout);

      // Structural chain correctness
      assert (sum == expS)
        else $error("sum bus mismatch: sum=%0h exp=%0h", sum, expS);
      assert (C[0] == c0) else $error("C[0] mismatch");
      assert (C[1] == c1) else $error("C[1] mismatch");
      assert (C[2] == c2) else $error("C[2] mismatch");

      // Outputs must be known when inputs are known
      assert (!$isunknown({S,Cout}))
        else $error("Unknown on outputs with known inputs");
    end

    // Targeted functional coverage
    cover (known_in && A==4'h0 && B==4'h0 && Cin==1'b0 && S==4'h0 && Cout==1'b0); // zero
    cover (known_in && A==4'hF && B==4'h1 && Cin==1'b0 && S==4'h0 && Cout==1'b1); // full ripple
    cover (known_in && A==4'h8 && B==4'h8 && Cin==1'b0 && S==4'h0 && Cout==1'b1); // MSB generate
    cover (known_in && A==4'hF && B==4'h0 && Cin==1'b1 && S==4'h0 && Cout==1'b1); // ripple from Cin
    cover (known_in && A==4'b0011 && B==4'b0001 && Cin==1'b0 && S==4'b0100 && Cout==1'b0); // 2-bit propagate
  end
endchecker

bind ripple_adder_4bit ripple_adder_4bit_sva ra4b_sva();

checker full_adder_sva;
  logic known_in;
  always_comb begin
    known_in = !$isunknown({a,b,cin});
    if (known_in) begin
      assert ({cout,sum} == a + b + cin)
        else $error("FA mismatch: a=%0b b=%0b cin=%0b -> sum=%0b cout=%0b",
                    a,b,cin,sum,cout);
      assert (sum  == (a ^ b ^ cin)) else $error("FA sum XOR mismatch");
      assert (cout == ((a & b) | (a & cin) | (b & cin))) else $error("FA cout majority mismatch");
    end

    // Exhaustive input coverage for 1-bit FA
    cover (known_in && {a,b,cin}==3'b000);
    cover (known_in && {a,b,cin}==3'b001);
    cover (known_in && {a,b,cin}==3'b010);
    cover (known_in && {a,b,cin}==3'b011);
    cover (known_in && {a,b,cin}==3'b100);
    cover (known_in && {a,b,cin}==3'b101);
    cover (known_in && {a,b,cin}==3'b110);
    cover (known_in && {a,b,cin}==3'b111);
  end
endchecker

bind full_adder full_adder_sva fa_sva();

`endif