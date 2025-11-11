// SVA checker for Multiplier. Bind this to the DUT.
// Focus: functional correctness, internal-partials consistency, and concise coverage.

module Multiplier_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [7:0] C,
  // internal DUT nets (bound hierarchically)
  input  logic [3:0] B0, B1, B2, B3,
  input  logic [7:0] P0, P1, P2, P3
);

  // reference shift-add product (combinational)
  function automatic logic [7:0] ref_prod(input logic [3:0] a, input logic [3:0] b);
    ref_prod =
      (b[0] ? {4'b0,a}       : 8'b0) +
      (b[1] ? ({4'b0,a} << 1): 8'b0) +
      (b[2] ? ({4'b0,a} << 2): 8'b0) +
      (b[3] ? ({4'b0,a} << 3): 8'b0);
  endfunction

  always @* begin
    // Unknowns: if inputs known, output must be known
    if (!$isunknown({A,B})) begin
      // Golden functionality
      assert (C == (A*B))
        else $error("Multiplier mismatch: C=%0d A=%0d B=%0d exp=%0d", C, A, B, A*B);

      // Equivalent shift-add implementation
      automatic logic [7:0] ssum = ref_prod(A,B);
      assert (C == ssum)
        else $error("Shift-add mismatch: C=%0d A=%0d B=%0d exp=%0d", C, A, B, ssum);

      // Range (max 15*15 = 225)
      assert (C <= 8'd225)
        else $error("Out-of-range result: C=%0d A=%0d B=%0d", C, A, B);
    end

    // Algebraic corner-cases
    if (!$isunknown({A,B}) && ((A==0) || (B==0)))
      assert (C == 8'd0) else $error("Zero rule violated: A=%0d B=%0d C=%0d", A,B,C);

    if (!$isunknown({A,B}) && (A==4'd1))
      assert (C == {4'b0,B}) else $error("Identity A==1 violated: B=%0d C=%0d", B,C);

    if (!$isunknown({A,B}) && (B==4'd1))
      assert (C == {4'b0,A}) else $error("Identity B==1 violated: A=%0d C=%0d", A,C);

    // Internal decomposition checks (intended spec): each Bk should be zero-extended B[k]
    assert (B0 === {3'b0, B[0]}) else $error("B0 split wrong: B0=%b B=%b", B0, B);
    assert (B1 === {3'b0, B[1]}) else $error("B1 split wrong: B1=%b B=%b", B1, B);
    assert (B2 === {3'b0, B[2]}) else $error("B2 split wrong: B2=%b B=%b", B2, B);
    assert (B3 === {3'b0, B[3]}) else $error("B3 split wrong: B3=%b B=%b", B3, B);

    // Internal partial products must match spec w.r.t. B bits
    assert (P0 === (A * {3'b0, B[0]})) else $error("P0 wrong: P0=%0d A=%0d B[0]=%0b", P0, A, B[0]);
    assert (P1 === (A * {3'b0, B[1]})) else $error("P1 wrong: P1=%0d A=%0d B[1]=%0b", P1, A, B[1]);
    assert (P2 === (A * {3'b0, B[2]})) else $error("P2 wrong: P2=%0d A=%0d B[2]=%0b", P2, A, B[2]);
    assert (P3 === (A * {3'b0, B[3]})) else $error("P3 wrong: P3=%0d A=%0d B[3]=%0b", P3, A, B[3]);

    // Basic functional coverage (concise but meaningful)
    cover (A==4'd0);
    cover (B==4'd0);
    cover (A==4'd1);
    cover (B==4'd1);
    cover (A==4'hF && B==4'hF);     // max*max
    cover (B==4'b0001);             // engages P0 path
    cover (B==4'b0010);             // engages P1 path
    cover (B==4'b0100);             // engages P2 path
    cover (B==4'b1000);             // engages P3 path
    cover (C[7]);                   // high MSB seen (large products)
    cover (P0!=0);
    cover (P1!=0);
    cover (P2!=0);
    cover (P3!=0);
  end

endmodule

// Bind into the DUT (accesses internal nets by name)
bind Multiplier Multiplier_sva u_multiplier_sva (
  .A (A),
  .B (B),
  .C (C),
  .B0(B0), .B1(B1), .B2(B2), .B3(B3),
  .P0(P0), .P1(P1), .P2(P2), .P3(P3)
);