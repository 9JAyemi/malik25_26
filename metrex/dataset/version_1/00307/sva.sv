// SVA for max_finder: verifies combinational behavior and provides concise coverage.
// Bind this file alongside the DUT.

module max_finder_sva;
  // This module is intended to be bound into max_finder and directly reference its signals:
  // D, max, shifted_D, highest_bit

  // Core functional checks (combinational)
  always @* begin
    // Input sanity
    assert (!$isunknown(D))
      else $error("max_finder: D has X/Z: %0h", D);

    // Internal consistency
    assert (highest_bit == D[15:12])
      else $error("max_finder: highest_bit=%0d exp=%0d D=%0h", highest_bit, D[15:12], D);

    assert (shifted_D == (D >> highest_bit))
      else $error("max_finder: shifted_D=%0h exp=%0h D=%0h highest_bit=%0d",
                  shifted_D, (D >> highest_bit), D, highest_bit);

    // Output correctness (two equivalent checks)
    assert (max == shifted_D)
      else $error("max_finder: max=%0h shifted_D=%0h D=%0h", max, shifted_D, D);

    assert (max == (D >> D[15:12]))
      else $error("max_finder: max=%0h exp=%0h D=%0h", max, (D >> D[15:12]), D);
  end

  // Coverage: exercise input extremes, shift-nibble space, and key outcomes
  always @* begin
    // Extremal and interesting inputs
    cover (D == 16'h0000);
    cover (D == 16'hFFFF);
    cover (D == 16'h8000);

    // Key behaviors for top-nibble 0,1,15
    cover (D[15:12] == 4'd0 && max == D);
    cover (D[15:12] == 4'd1 && max == (D >> 1));
    cover (D[15:12] == 4'd15 && max == (D >> 15));

    // Full nibble coverage (0..15)
    integer i;
    for (i = 0; i < 16; i++) begin
      cover (highest_bit == i[3:0]);
    end
  end
endmodule

bind max_finder max_finder_sva mfsva();