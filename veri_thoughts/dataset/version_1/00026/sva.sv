// SVA checker for bin2gray
module bin2gray_sva (input logic [3:0] bin, input logic [3:0] gray);

  function automatic logic [3:0] gray_func (input logic [3:0] b);
    return b ^ (b >> 1);
  endfunction

  // X/Z checks
  a_no_x_bin:  assert property (@(bin)                 !$isunknown(bin));
  a_no_x_gray: assert property (@(bin or gray) !$isunknown(bin) |-> !$isunknown(gray));

  // Functional equivalence
  a_gray_eq:   assert property (@(bin or gray) gray == gray_func(bin));

  // No combinational lag on input change
  a_no_lag:    assert property (@(bin) $changed(bin) |-> ##0 (gray == gray_func(bin)));

  // If bin steps by +/-1 (mod 16), Gray must change by exactly 1 bit
  a_adjacent_step: assert property (@(bin)
      !$isunknown($past(bin)) && !$isunknown(bin) &&
      ((bin == $past(bin) + 4'd1) || (bin + 4'd1 == $past(bin))))
    |-> $countones(gray ^ $past(gray)) == 1;

  // Coverage: hit all 16 input codes
  generate
    genvar v;
    for (v = 0; v < 16; v++) begin : g_bin_vals
      c_bin_val: cover property (@(bin) bin == 4'(v));
    end
  endgenerate

  // Coverage: each gray bit rises and falls at least once
  generate
    genvar k;
    for (k = 0; k < 4; k++) begin : g_gray_toggles
      c_gray_rise: cover property (@(bin or gray) $rose(gray[k]));
      c_gray_fall: cover property (@(bin or gray) $fell(gray[k]));
    end
  endgenerate

endmodule

// Bind to DUT
bind bin2gray bin2gray_sva sva_inst (.bin(bin), .gray(gray));