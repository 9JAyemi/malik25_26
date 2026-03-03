// SVA checker for desxor1
module desxor1_sva(
  input logic clk,
  input logic [47:0] e, k,
  input logic [5:0] b1x, b2x, b3x, b4x, b5x, b6x, b7x, b8x
);

  default clocking cb @(posedge clk); endclocking

  let OUT48 = {b8x,b7x,b6x,b5x,b4x,b3x,b2x,b1x};
  let IN48  = (k ^ e);

  // Functional equivalence (also checks correct slicing/order)
  a_equiv: assert property (OUT48 === IN48);

  // Known-propagation: known inputs imply known outputs
  a_known: assert property (!$isunknown({e,k}) |-> !$isunknown(OUT48));

  // Past-valid for temporal checks
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  let D_OUT = OUT48 ^ $past(OUT48);
  let D_E   = e      ^ $past(e);
  let D_K   = k      ^ $past(k);

  // Bit-independence: single-bit toggle in one input maps 1:1 to output
  a_indep_e: assert property (disable iff(!past_valid)
                              !$isunknown({e,k,$past(e),$past(k)}) &&
                              $stable(k) && $onehot(D_E)
                              |-> (D_OUT == D_E));

  a_indep_k: assert property (disable iff(!past_valid)
                              !$isunknown({e,k,$past(e),$past(k)}) &&
                              $stable(e) && $onehot(D_K)
                              |-> (D_OUT == D_K));

  // Concise functional coverage
  c_all_zero: cover property (OUT48 == 48'h0);
  c_all_ones: cover property (OUT48 == 48'hFFFFFFFFFFFF);
  c_flip_lsb: cover property (disable iff(!past_valid) $stable(k) && (D_E == 48'h1));
  c_flip_msb: cover property (disable iff(!past_valid) $stable(k) && (D_E == 48'h8000_0000_0000));

endmodule

// Example bind (connect clk from your TB):
// bind desxor1 desxor1_sva u_desxor1_sva(.clk(tb_clk), .e(e), .k(k),
//   .b1x(b1x), .b2x(b2x), .b3x(b3x), .b4x(b4x), .b5x(b5x), .b6x(b6x), .b7x(b7x), .b8x(b8x));