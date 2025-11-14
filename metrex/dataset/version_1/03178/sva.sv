// SVA checker for mult4. Bind this to the DUT:  bind mult4 mult4_sva m4_sva (.*);
module mult4_sva (
  input logic a0, a1, a2, a3,
  input logic b0, b1, b2, b3,
  input logic z0, z1, z2, z3, z4, z5, z6, z7
);
  // Canonical operand/result views
  wire [3:0] A = {a3,a2,a1,a0};
  wire [3:0] B = {b3,b2,b1,b0};
  wire [7:0] Z = {z7,z6,z5,z4,z3,z2,z1,z0};

  // Combinational correctness (defer one delta to avoid transient hazards)
  always @* begin
    if (!$isunknown({A,B})) begin
      assert (#0 (Z === (A*B))) else
        $error("mult4 product mismatch: A=%0d B=%0d Z=%0d exp=%0d", A, B, Z, A*B);
      assert (#0 (!$isunknown(Z))) else
        $error("mult4 produced X/Z on output for known inputs: A=%b B=%b Z=%b", A, B, Z);
    end
  end

  // Critical local invariant (helps debug bit-ordering quickly)
  always @* if (!$isunknown({a0,b0})) assert (#0 (z0 === (a0 & b0))) else
    $error("mult4 LSB mismatch: z0 != a0&b0 (a0=%b b0=%b z0=%b)", a0, b0, z0);

  // Algebraic sanity
  always @* if ((A==0 || B==0) && !$isunknown({A,B}))
    assert (#0 (Z==0)) else if ((A==0 || B==0) && !$isunknown({A,B}))
    $error("mult4 zero-input rule violated: A=%0d B=%0d Z=%0d", A, B, Z);

  // Lightweight functional coverage (samples on any input change)
  // Corner cases
  cover property (@(posedge $changed({A,B})) (A==0 && B==0 && Z==0));
  cover property (@(posedge $changed({A,B})) (A==4'hF && B==4'hF && Z==8'd225));
  cover property (@(posedge $changed({A,B})) (A==1 && Z==B));
  cover property (@(posedge $changed({A,B})) (B==1 && Z==A));
  // Each output bit seen 0 and 1 sometime
  genvar i;
  generate
    for (i=0;i<8;i++) begin : cv_bits
      cover property (@(posedge $changed({A,B})) (Z[i]==1'b0));
      cover property (@(posedge $changed({A,B})) (Z[i]==1'b1));
    end
  endgenerate
endmodule

// Recommended bind (place in a package or a separate file included by your testbench)
// bind mult4 mult4_sva m4_sva (.*);