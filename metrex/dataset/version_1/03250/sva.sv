// SVA for barrel_shifter
// Assumes intended spec: 16-bit rotate-left by B
// Bind this to the DUT; assertions are combinational and sample after delta

module barrel_shifter_sva #(parameter WIDTH=16)
(
  input  logic [WIDTH-1:0] A,
  input  logic [3:0]       B,
  input  logic [WIDTH-1:0] Y
);

  function automatic logic [WIDTH-1:0] rol16 (input logic [WIDTH-1:0] a, input logic [3:0] s);
    rol16 = (a << s) | (a >> (WIDTH - s));
  endfunction

  // Core functional spec
  assert property (@(A or B) disable iff ($isunknown({A,B})) ##0 (Y == rol16(A,B)))
    else $error("barrel_shifter: Y != rotate-left(A,B)");

  // Simple corner
  assert property (@(A or B) disable iff ($isunknown({A,B})) ##0 ((B==0) |-> (Y==A)));

  // X-propagation guard (when inputs known)
  assert property (@(A or B) disable iff ($isunknown({A,B})) ##0 (!$isunknown(Y)));

  // Rotation preserves popcount
  assert property (@(A or B) disable iff ($isunknown({A,B})) ##0 ($countones(Y) == $countones(A)));

  // Coverage: every shift amount exercised and matches spec
  genvar i;
  generate
    for (i=0; i<16; i++) begin : gen_cov_b
      cover property (@(A or B) ##0 (B==i) && (Y == rol16(A,B)));
    end
  endgenerate

  // Coverage: a few useful A patterns
  cover property (@(A or B) ##0 (A=={WIDTH{1'b0}}));
  cover property (@(A or B) ##0 (A=={WIDTH{1'b1}}));
  cover property (@(A or B) ##0 $onehot(A));
  cover property (@(A or B) ##0 $onehot0(A));

endmodule

bind barrel_shifter barrel_shifter_sva sva (.A(A), .B(B), .Y(Y));