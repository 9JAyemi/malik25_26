// SVA checker for ABS; bind this to the DUT
module ABS_sva #(parameter int n = 8)
(
  input  signed [n-1:0] in,
  output signed [n-1:0] out
);
  localparam signed [n-1:0] MIN_NEG = {1'b1, {n-1{1'b0}}};
  localparam signed [n-1:0] MAX_POS = {1'b0, {n-1{1'b1}}};

  // Avoid vacuous passes when X/Z present; separately flag X/Z below
  default disable iff ($isunknown({in,out}));

  // Functional correctness (concise equivalence to absolute-value expression)
  assert property ( out == (in[n-1] ? (~in + 1) : in) );

  // Corner cases and invariants
  assert property ( in == 0 |-> out == 0 );
  assert property ( in == MIN_NEG |-> out == MIN_NEG );
  assert property ( (in < 0 && in != MIN_NEG) |-> out >= 0 );
  assert property ( out < 0 |-> (out == MIN_NEG && in == MIN_NEG) );

  // X/Z policy: clean inputs imply clean outputs
  assert property ( !$isunknown(in) |-> !$isunknown(out) );

  // Coverage: exercise both paths and key boundaries
  cover property ( (in > 0) && (out == in) );
  cover property ( (in < 0) && (in != MIN_NEG) && (out == (~in + 1)) );
  cover property ( in == 0 && out == 0 );
  cover property ( in == MIN_NEG && out == MIN_NEG );
  cover property ( in == MAX_POS && out == MAX_POS );
  cover property ( in == -1 && out == 1 );
endmodule

bind ABS ABS_sva #(.n(n)) ABS_sva_i (.in(in), .out(out));