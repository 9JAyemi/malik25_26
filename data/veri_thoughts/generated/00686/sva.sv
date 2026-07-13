module binary_to_gray_converter_sva (
  input logic clk,
  input logic areset,
  input logic [3:0] bin,
  input logic [3:0] gray
);
  ///// Reset behavior /////
  // While reset is asserted (active-low), gray must be zero at the sampling edge.
  check_reset_drives_gray_zero: assert property (
    @(posedge clk) !areset |-> (gray == 4'b0000)
  );

  // First cycle after reset release, gray still holds zero.
  check_gray_zero_first_cycle_after_reset: assert property (
    @(posedge clk) disable iff (!areset) $past(!areset) |-> (gray == 4'b0000)
  );

  ///// Functional mapping (one-cycle latency) /////
  // In non-reset, gray equals previous cycle's bin ^ (bin>>1).
  check_gray_matches_prev_bin_transform: assert property (
    @(posedge clk) disable iff (!areset) $past(areset) |-> (gray == ($past(bin) ^ ($past(bin) >> 1)))
  );

  // MSB mapping: gray[3] equals previous bin[3].
  check_gray_bit3_maps: assert property (
    @(posedge clk) disable iff (!areset) $past(areset) |-> (gray[3] == $past(bin[3]))
  );

  // gray[2] equals previous bin[2] XOR bin[3].
  check_gray_bit2_maps: assert property (
    @(posedge clk) disable iff (!areset) $past(areset) |-> (gray[2] == ($past(bin[2]) ^ $past(bin[3])))
  );

  // gray[1] equals previous bin[1] XOR bin[2].
  check_gray_bit1_maps: assert property (
    @(posedge clk) disable iff (!areset) $past(areset) |-> (gray[1] == ($past(bin[1]) ^ $past(bin[2])))
  );

  // gray[0] equals previous bin[0] XOR bin[1].
  check_gray_bit0_maps: assert property (
    @(posedge clk) disable iff (!areset) $past(areset) |-> (gray[0] == ($past(bin[0]) ^ $past(bin[1])))
  );

  ///// Stability under stable inputs /////
  // If bin was stable over the last two cycles (and not in reset), gray is stable over the last cycle.
  check_gray_stable_when_bin_stable: assert property (
    @(posedge clk) disable iff (!areset)
      $past(areset,2) && $past(areset,1) && ($past(bin,1) == $past(bin,2))
      |-> (gray == $past(gray))
  );
endmodule