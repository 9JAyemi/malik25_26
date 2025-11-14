// SVA bind file for mult4
// Concise, high-quality checks and coverage for a 4x4 combinational multiplier.

module mult4_sva (
  input a0,a1,a2,a3,
  input b0,b1,b2,b3,
  input z0,z1,z2,z3,z4,z5,z6,z7
);
  // Vectorize
  wire [3:0] A = {a3,a2,a1,a0};
  wire [3:0] B = {b3,b2,b1,b0};
  wire [7:0] Z = {z7,z6,z5,z4,z3,z2,z1,z0};

  // Functional correctness
  assert property (@(*)) (Z == (A * B));

  // Basic bit sanity
  assert property (@(*)) (z0 == (a0 & b0));

  // Knownness: if inputs are known, outputs must be known
  assert property (@(*)) (!$isunknown({A,B}) |-> !$isunknown(Z));

  // Algebraic corner cases
  assert property (@(*)) ((A==4'd0 || B==4'd0) |-> (Z==8'd0));
  assert property (@(*)) ((A==4'd1) |-> (Z=={4'b0000,B}));
  assert property (@(*)) ((B==4'd1) |-> (Z=={4'b0000,A}));

  // Range (max 15*15 = 225 = 8'hE1)
  assert property (@(*)) (Z <= 8'hE1);

  // Coverage: key scenarios
  cover property (@(*)) (A==4'd0 && B==4'd0 && Z==8'd0);
  cover property (@(*)) (A==4'd1 && Z=={4'b0000,B});
  cover property (@(*)) (B==4'd1 && Z=={4'b0000,A});
  cover property (@(*)) (A==4'd15 && B==4'd15 && Z==8'hE1);
  cover property (@(*)) (Z[7] == 1'b1); // overflow bit exercised

  // Coverage: each output bit toggles at least once
  genvar i;
  generate
    for (i=0; i<8; i++) begin : z_toggle_cov
      cover property (@(*)) $rose(Z[i]);
      cover property (@(*)) $fell(Z[i]);
    end
  endgenerate
endmodule

bind mult4 mult4_sva mult4_sva_i (.*);