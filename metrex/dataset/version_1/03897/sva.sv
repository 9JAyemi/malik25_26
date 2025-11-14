// SVA for concat_split_vectors
// Concise, bound-in checker. Uses ##0 to avoid delta-cycle races.

module concat_split_vectors_sva (
  input  [7:0] a,
  input  [7:0] b,
  input  [3:0] w,
  input  [3:0] x,
  input  [3:0] y,
  input  [3:0] z
);
  wire [15:0] in  = {a,b};
  wire [15:0] sum = in + 16'd3;

  // Functional equivalence and split correctness
  a_sum_ok:      assert property (@(a or b) ##0 ({w,x,y,z} === sum));
  a_nibbles_ok:  assert property (@(a or b) ##0 (w===sum[15:12] && x===sum[11:8] && y===sum[7:4] && z===sum[3:0]));

  // Internal concat must reflect inputs (relies on bind into DUT scope)
  a_concat_ok:   assert property (@(a or b) ##0 (concat === in));

  // Knownness: known inputs -> known outputs
  a_known:       assert property (@(a or b) (!$isunknown(in)) |-> ##0 (!$isunknown({w,x,y,z})));

  // Coverage: key corners and carry propagation across nibbles
  c_zero:  cover property (@(a or b) ##0 (in==16'h0000 && {w,x,y,z}==16'h0003));
  c_max:   cover property (@(a or b) ##0 (in==16'hFFFF && {w,x,y,z}==16'h0002));

  // LSB nibble no-carry vs carry, and chained carries
  c_no_cy: cover property (@(a or b) ##0 (in[3:0] <= 4'hC));
  c_cy1:   cover property (@(a or b) ##0 (in[3:0] >= 4'hD));                                 // z -> y
  c_cy2:   cover property (@(a or b) ##0 (in[3:0] >= 4'hD && in[7:4]==4'hF));                // z->y then y -> x
  c_cy3:   cover property (@(a or b) ##0 (in[3:0] >= 4'hD && in[7:4]==4'hF && in[11:8]==4'hF)); // up to w
  c_wrap:  cover property (@(a or b) ##0 (in[3:0] >= 4'hD && in[7:4]==4'hF && in[11:8]==4'hF &&
                                           in[15:12]==4'hF && {w,x,y,z}==16'h0002));
endmodule

bind concat_split_vectors concat_split_vectors_sva sva_inst (.a(a), .b(b), .w(w), .x(x), .y(y), .z(z));