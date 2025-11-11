// SVA for four_bit_adder and full_adder (concise, full functional and structural checks)
// Bind these checkers in your simulation/formal environment.

module four_bit_adder_sva (four_bit_adder dut);
  always_comb begin
    automatic logic [4:0] exp = dut.A + dut.B + dut.Cin;

    // Clean inputs -> clean, correct outputs
    if (!$isunknown({dut.A,dut.B,dut.Cin})) begin
      assert (!$isunknown({dut.S,dut.Cout})) else $error("X/Z on outputs with clean inputs");
      assert ({dut.Cout,dut.S} == exp) else $error("{Cout,S} mismatch exp=%0d", exp);
    end

    // Structural ripple checks (stage-by-stage) + tie-off of S
    assert (dut.S == dut.sum) else $error("S not tied to internal sum");

    assert (dut.sum[0] == (dut.A[0]^dut.B[0]^dut.Cin)) else $error("sum[0] mismatch");
    assert (dut.C1     == ((dut.A[0]&dut.B[0]) | (dut.A[0]&dut.Cin) | (dut.B[0]&dut.Cin))) else $error("C1 mismatch");

    assert (dut.sum[1] == (dut.A[1]^dut.B[1]^dut.C1)) else $error("sum[1] mismatch");
    assert (dut.C2     == ((dut.A[1]&dut.B[1]) | (dut.A[1]&dut.C1) | (dut.B[1]&dut.C1))) else $error("C2 mismatch");

    assert (dut.sum[2] == (dut.A[2]^dut.B[2]^dut.C2)) else $error("sum[2] mismatch");
    assert (dut.C3     == ((dut.A[2]&dut.B[2]) | (dut.A[2]&dut.C2) | (dut.B[2]&dut.C2))) else $error("C3 mismatch");

    assert (dut.sum[3] == (dut.A[3]^dut.B[3]^dut.C3)) else $error("sum[3] mismatch");
    assert (dut.Cout   == ((dut.A[3]&dut.B[3]) | (dut.A[3]&dut.C3) | (dut.B[3]&dut.C3))) else $error("Cout mismatch");

    // Compact functional coverage (immediate cover)
    automatic logic p0 = dut.A[0]^dut.B[0];
    automatic logic p1 = dut.A[1]^dut.B[1];
    automatic logic p2 = dut.A[2]^dut.B[2];
    automatic logic p3 = dut.A[3]^dut.B[3];

    cover (exp[4]);                       // overflow
    cover (exp == 5'd0);                  // zero result
    cover (p0 & p1 & p2 & p3 & dut.Cin);  // full propagate chain
    cover (dut.C1 & dut.C2 & dut.C3 & dut.Cout); // carry ripples all the way
  end
endmodule

bind four_bit_adder four_bit_adder_sva sva_four_bit_adder();

// Generic checker for the leaf full_adder as well
module full_adder_sva (full_adder f);
  always_comb begin
    if (!$isunknown({f.a,f.b,f.cin})) begin
      assert (!$isunknown({f.sum,f.cout})) else $error("full_adder X/Z outputs with clean inputs");
      assert (f.sum  == (f.a^f.b^f.cin)) else $error("full_adder sum mismatch");
      assert (f.cout == ((f.a&f.b)|(f.a&f.cin)|(f.b&f.cin))) else $error("full_adder cout mismatch");
    end
    // Small truth-table coverage
    cover ({f.a,f.b,f.cin} == 3'b000);
    cover ({f.a,f.b,f.cin} == 3'b111);
    cover (f.cout); // any carry-out
  end
endmodule

bind full_adder full_adder_sva sva_full_adder();