// SVA checker for count_even
// Binds into the DUT to verify functionality and provide concise coverage.

module count_even_sva;
  // Visible in bound scope: in, out, even_count
  localparam [255:0] EVEN_MASK = {128{2'b01}}; // 1s on even indices: 0,2,...,254

  default clocking cb @(*); endclocking

  // Core functional spec: out == popcount(even bits) mod 16
  assert property (out == $countones(in & EVEN_MASK)[3:0]);

  // Internal tally must equal exact popcount of even bits
  assert property (even_count == $countones(in & EVEN_MASK)[7:0]);

  // No X/Z on out when inputs are known
  assert property (!$isunknown(in) |-> !$isunknown(out));

  // Coverage: observe each possible nibble value on out with matching count
  genvar v;
  for (v = 0; v < 16; v++) begin : cov_out_vals
    cover property (($countones(in & EVEN_MASK) == v) && (out == v[3:0]));
  end

  // Coverage: wrap-around cases
  cover property (($countones(in & EVEN_MASK) == 16) && (out == 4'd0));   // first wrap
  cover property ((in == '0) && (out == 4'd0));                           // all zeros
  cover property (((in & EVEN_MASK) == EVEN_MASK) && (out == 4'd0));      // all even bits set (128) -> 0
endmodule

bind count_even count_even_sva sva_i();