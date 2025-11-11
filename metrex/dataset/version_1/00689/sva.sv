// SVA checker for bin_to_gray
module bin_to_gray_sva (
  input logic [3:0] bin_in,
  input logic [3:0] gray_out
);

  // Functional equivalence (vector form)
  // This DUT implements g = b ^ (b << 1) with LSB-anchored Gray mapping
  assert property (@(*) gray_out == (bin_in ^ (bin_in << 1)))
    else $error("bin_to_gray mapping mismatch");

  // X-propagation sanity: if inputs are known, outputs must be known
  assert property (@(*) (!$isunknown(bin_in)) |-> ##0 !$isunknown(gray_out))
    else $error("Unknown X/Z on gray_out with known bin_in");

  // Sensitivity/independence checks: only the intended gray bits may change
  // when exactly one input bit toggles.
  assert property (@(*) ($changed(bin_in[0]) && $stable(bin_in[3:1]))
                   |-> ##0 $changed(gray_out[0]) && $changed(gray_out[1]) && $stable(gray_out[3:2]))
    else $error("Unexpected gray_out response to bin_in[0] change");

  assert property (@(*) ($changed(bin_in[1]) && $stable({bin_in[3:2],bin_in[0]}))
                   |-> ##0 $changed(gray_out[1]) && $changed(gray_out[2]) && $stable({gray_out[3],gray_out[0]}))
    else $error("Unexpected gray_out response to bin_in[1] change");

  assert property (@(*) ($changed(bin_in[2]) && $stable({bin_in[3],bin_in[1:0]}))
                   |-> ##0 $changed(gray_out[2]) && $changed(gray_out[3]) && $stable(gray_out[1:0]))
    else $error("Unexpected gray_out response to bin_in[2] change");

  assert property (@(*) ($changed(bin_in[3]) && $stable(bin_in[2:0]))
                   |-> ##0 $changed(gray_out[3]) && $stable(gray_out[2:0]))
    else $error("Unexpected gray_out response to bin_in[3] change");

  // Coverage: see all 16 input combinations
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_BIN_VALUES
      cover property (@(*) bin_in == i[3:0]);
    end
  endgenerate

  // Coverage: each gray bit toggles at least once
  genvar j;
  generate
    for (j = 0; j < 4; j++) begin : C_GRAY_TOGGLES
      cover property (@(*) $changed(gray_out[j]));
    end
  endgenerate

endmodule

// Bind into the DUT
bind bin_to_gray bin_to_gray_sva u_bin_to_gray_sva (.bin_in(bin_in), .gray_out(gray_out));