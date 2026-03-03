// SVA for binary_to_gray
// Bind this to the DUT to check/cover functionality concisely

`ifndef BINARY_TO_GRAY_SVA
`define BINARY_TO_GRAY_SVA

module binary_to_gray_sva (input logic clk, input logic [3:0] binary, input logic [3:0] gray);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Core functional check (sample after NBA with ##0)
  a_core_func: assert property (##0 (gray == (binary ^ (binary >> 1))))
    else $error("binary_to_gray: mismatch gray=%0h, binary=%0h", gray, binary);

  // If input stable across cycles, output must be stable
  a_stability: assert property (disable iff (!past_valid)
                                $stable(binary) |-> ##0 $stable(gray))
    else $error("binary_to_gray: gray changed while binary stable");

  // Known-in -> known-out
  a_no_x_out: assert property ( !$isunknown(binary) |-> ##0 !$isunknown(gray))
    else $error("binary_to_gray: X/Z on gray with known binary");

  // +1 (mod 16) on binary => Hamming distance 1 on gray
  a_hd1_inc: assert property (disable iff (!past_valid)
                              ((binary == ($past(binary) + 4'd1)) ||
                               ($past(binary) == 4'hF && binary == 4'h0))
                              |-> ##0 ($countones(gray ^ $past(gray)) == 1))
    else $error("binary_to_gray: +1 step did not toggle exactly one gray bit");

  // -1 (mod 16) on binary => Hamming distance 1 on gray
  a_hd1_dec: assert property (disable iff (!past_valid)
                              ((binary == ($past(binary) - 4'd1)) ||
                               ($past(binary) == 4'h0 && binary == 4'hF))
                              |-> ##0 ($countones(gray ^ $past(gray)) == 1))
    else $error("binary_to_gray: -1 step did not toggle exactly one gray bit");

  // Coverage: see +/-1 transitions; each gray bit toggles at least once
  c_inc: cover property (disable iff (!past_valid)
                         ((binary == ($past(binary) + 4'd1)) ||
                          ($past(binary) == 4'hF && binary == 4'h0)));

  c_dec: cover property (disable iff (!past_valid)
                         ((binary == ($past(binary) - 4'd1)) ||
                          ($past(binary) == 4'h0 && binary == 4'hF)));

  genvar i;
  generate
    for (i=0; i<4; i++) begin : cov_bit_toggles
      c_gray_bit_toggle: cover property (##0 $changed(gray[i]));
    end
  endgenerate

endmodule

// Bind into DUT
bind binary_to_gray binary_to_gray_sva u_binary_to_gray_sva (
  .clk   (clk),
  .binary(binary),
  .gray  (gray)
);

`endif