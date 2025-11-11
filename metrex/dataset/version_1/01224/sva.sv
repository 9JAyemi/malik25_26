// SVA for binary_to_gray. Bind this to the DUT.
// Uses $global_clock for sampling; replace with a real clock if desired.

module binary_to_gray_sva (
  input logic [7:0] bin_in,
  input logic [7:0] gray_out,
  input logic [7:0] bin_to_gray // internal net from DUT (bound by name)
);
  default clocking cb @($global_clock); endclocking

  function automatic logic [7:0] bin2gray (input logic [7:0] b);
    return b ^ {b[7], b[7:1]};
  endfunction

  function automatic logic [7:0] gray2bin (input logic [7:0] g);
    logic [7:0] b;
    b[7] = g[7];
    for (int i = 6; i >= 0; i--) b[i] = b[i+1] ^ g[i];
    return b;
  endfunction

  // Combinational correctness
  assert property (bin2gray(bin_in) == gray_out)
    else $error("binary_to_gray: forward mapping incorrect");

  assert property (gray2bin(gray_out) == bin_in)
    else $error("binary_to_gray: inverse mapping incorrect");

  // Internal reverse wire should implement true Gray->Binary (this will flag the current bug)
  assert property (bin_to_gray == gray2bin(gray_out))
    else $error("binary_to_gray: internal bin_to_gray is not true Gray->Binary");

  // Clean inputs produce clean outputs
  assert property (!$isunknown(bin_in) |-> !$isunknown(gray_out))
    else $error("binary_to_gray: X/Z on gray_out with known bin_in");

  // If binary increments by 1 between samples, Gray must toggle exactly one bit
  assert property (($past(bin_in) + 8'd1 == bin_in) |-> $countones(gray_out ^ $past(gray_out)) == 1)
    else $error("binary_to_gray: Gray did not toggle 1 bit on +1 binary step");

  // Coverage
  cover property (bin_in == 8'h00 && gray_out == bin2gray(8'h00));
  cover property (bin_in == 8'hFF && gray_out == bin2gray(8'hFF));
  generate
    for (genvar i = 0; i < 8; i++) begin : COV_GBIT_TOGGLE
      cover property ($changed(gray_out[i]));
    end
    // Observe at least one +1 binary step producing a 1-bit Gray toggle
    cover property (($past(bin_in) + 8'd1 == bin_in) && ($countones(gray_out ^ $past(gray_out)) == 1));
  endgenerate
endmodule

// Bind into the DUT (allows access to internal wire bin_to_gray)
bind binary_to_gray binary_to_gray_sva b2g_sva (
  .bin_in(bin_in),
  .gray_out(gray_out),
  .bin_to_gray(bin_to_gray)
);