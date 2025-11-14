// SVA for four_bit_adder and full_adder
// Bind these to the DUTs; no changes to RTL required.

module four_bit_adder_sva(four_bit_adder dut);

  // Compute expected ripple carries purely from A,B,Cin (no DUT internals)
  function automatic logic [4:0] exp_carries(input logic [3:0] a, b, input logic cin);
    logic [3:0] p, g;
    logic [4:0] c;
    int i;
    p = a ^ b;
    g = a & b;
    c[0] = cin;
    for (i = 0; i < 4; i++) c[i+1] = g[i] | (p[i] & c[i]);
    return c;
  endfunction

  // Functional correctness and internal carry chain checks (only when inputs are known)
  always_comb begin
    if (!$isunknown({dut.A, dut.B, dut.Cin})) begin
      logic [4:0] ec = exp_carries(dut.A, dut.B, dut.Cin);
      assert ({dut.Cout, dut.S} == dut.A + dut.B + dut.Cin)
        else $error("Adder mismatch A=%0h B=%0h Cin=%0b -> S=%0h Cout=%0b", dut.A, dut.B, dut.Cin, dut.S, dut.Cout);
      assert (dut.carry === ec[3:0]) else $error("Carry chain mismatch exp=%b got=%b", ec[3:0], dut.carry);
      assert (dut.Cout  === ec[4])   else $error("Final carry mismatch exp=%b got=%b", ec[4], dut.Cout);
      assert (!$isunknown({dut.S, dut.Cout, dut.carry}))
        else $error("Unknown outputs/carries with known inputs");
    end
  end

  // Corner/categoric coverage (trigger on any input change)
  cover property (@(dut.A or dut.B or dut.Cin)
    dut.A==4'h0 && dut.B==4'h0 && dut.Cin==1'b0 ##0 dut.S==4'h0 && dut.Cout==1'b0);
  cover property (@(dut.A or dut.B or dut.Cin)
    dut.A==4'hF && dut.B==4'hF && dut.Cin==1'b1 ##0 dut.S==4'hF && dut.Cout==1'b1);
  // Full ripple propagation across all 4 bits (both polarities)
  cover property (@(dut.A or dut.B or dut.Cin)
    dut.A==4'hF && dut.B==4'h0 && dut.Cin==1'b1 ##0 dut.carry==4'b111 && dut.S==4'h0 && dut.Cout);
  cover property (@(dut.A or dut.B or dut.Cin)
    dut.A==4'h0 && dut.B==4'hF && dut.Cin==1'b1 ##0 dut.carry==4'b111 && dut.S==4'h0 && dut.Cout);

  // Per-bit generate/kill/propagate coverage
  genvar k;
  generate
    for (k=0; k<4; k++) begin : bit_cov
      wire cin_k = (k==0) ? dut.Cin : dut.carry[k-1];
      // propagate: A^B=1 -> sum = ~cin
      cover property (@(dut.A or dut.B or dut.Cin)
        (dut.A[k]^dut.B[k]) ##0 (dut.S[k] == ~cin_k));
      // generate: A&B=1 -> carry out = 1
      cover property (@(dut.A or dut.B or dut.Cin)
        (dut.A[k]&dut.B[k]) ##0 ((k<3)? dut.carry[k] : dut.Cout));
      // kill: ~A&~B=1 -> carry out = 0 when cin=1 (implicit from propagate/kill chain)
      cover property (@(dut.A or dut.B or dut.Cin)
        (~dut.A[k]&~dut.B[k] & cin_k) ##0 ((k<3)? !dut.carry[k] : !dut.Cout));
    end
  endgenerate

endmodule

bind four_bit_adder four_bit_adder_sva SVA_TOP(.dut());

// Tight SVA on the leaf full_adder as well
module full_adder_sva(full_adder d);
  always_comb begin
    if (!$isunknown({d.a, d.b, d.cin})) begin
      assert ({d.cout, d.sum} == d.a + d.b + d.cin)
        else $error("FA mismatch a=%0b b=%0b cin=%0b -> sum=%0b cout=%0b", d.a, d.b, d.cin, d.sum, d.cout);
      assert (!$isunknown({d.sum, d.cout})) else $error("FA unknown outputs with known inputs");
    end
  end

  // Cover all 8 input combinations
  cover property (@(d.a or d.b or d.cin) {d.a,d.b,d.cin} == 3'b000);
  cover property (@(d.a or d.b or d.cin) {d.a,d.b,d.cin} == 3'b001);
  cover property (@(d.a or d.b or d.cin) {d.a,d.b,d.cin} == 3'b010);
  cover property (@(d.a or d.b or d.cin) {d.a,d.b,d.cin} == 3'b011);
  cover property (@(d.a or d.b or d.cin) {d.a,d.b,d.cin} == 3'b100);
  cover property (@(d.a or d.b or d.cin) {d.a,d.b,d.cin} == 3'b101);
  cover property (@(d.a or d.b or d.cin) {d.a,d.b,d.cin} == 3'b110);
  cover property (@(d.a or d.b or d.cin) {d.a,d.b,d.cin} == 3'b111);
endmodule

bind full_adder full_adder_sva FA_SVA(.d());