// SVA checker for binary_multiplier
// Binds to the DUT and checks unsigned 4x4=8 multiply, plus full input coverage.

module binary_multiplier_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic [7:0] out
);

  // Sample whenever inputs change
  event ab_ev;
  always @(a or b) -> ab_ev;
  default clocking cb @ (ab_ev); endclocking

  // No X on out when inputs are known
  assert property ( !$isunknown({a,b}) |-> !$isunknown(out) );

  // Functional spec: out == a * b (unsigned)
  assert property ( !$isunknown({a,b}) |-> out == (a * b) );

  // Equivalent partial-products form
  assert property (
    !$isunknown({a,b}) |-> out ==
      ( (a[0] ? {4'b0000, b}        : 8'd0) +
        (a[1] ? {3'b000,  b, 1'b0}  : 8'd0) +
        (a[2] ? {2'b00,   b, 2'b00} : 8'd0) +
        (a[3] ? {1'b0,    b, 3'b000}: 8'd0) )
  );

  // Useful corner cases
  assert property ( (a==4'd0) |-> out==8'd0 );
  assert property ( (b==4'd0) |-> out==8'd0 );
  assert property ( (a==4'd1) |-> out=={4'b0000,b} );
  assert property ( (b==4'd1) |-> out=={4'b0000,a} );
  assert property ( (a==4'd15 && b==4'd15) |-> out==8'd225 );

  // Full input-space coverage (256 points)
  genvar i,j;
  generate
    for (i=0;i<16;i++) begin : COV_A
      for (j=0;j<16;j++) begin : COV_B
        cover property ( a==i && b==j );
      end
    end
  endgenerate

  // Cover correct results observed
  cover property ( !$isunknown({a,b}) && out == (a*b) );

endmodule

// Bind into every instance of the DUT
bind binary_multiplier binary_multiplier_sva u_binary_multiplier_sva(.a(a), .b(b), .out(out));