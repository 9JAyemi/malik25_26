// Bind this SVA to the DUT
bind split_16bit_input split_16bit_input_sva();

// SVA module (binds into DUT scope; can see internal regs)
module split_16bit_input_sva;

  // Use DUT clock
  default clocking cb @(posedge clk); endclocking

  // Past-valid guard for $past()
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // 1. Pipeline capture: input_reg holds previous-cycle input
  assert property (disable iff (!past_valid)
                   input_reg == $past(in))
    else $error("input_reg must equal prior in");

  // 2. Byte-split correctness one cycle later
  assert property (disable iff (!past_valid)
                   upper_byte_reg == $past(in[15:8]) &&
                   lower_byte_reg == $past(in[7:0]))
    else $error("Byte split into regs incorrect");

  // 3. Combinational passthrough to outputs
  assert property (out_hi == upper_byte_reg && out_lo == lower_byte_reg)
    else $error("Outputs must match internal byte regs");

  // 4. End-to-end: outputs reflect prior-cycle input
  assert property (disable iff (!past_valid)
                   {out_hi,out_lo} == $past(in))
    else $error("Outputs must equal prior in");

  // Coverage: exercise propagation and both/each byte updates
  cover property (past_valid && in != $past(in) ##1 {out_hi,out_lo} == $past(in));
  cover property (past_valid && in[15:8] != $past(in[15:8]) && in[7:0] == $past(in[7:0])
                  ##1 out_hi == $past(in[15:8]) && out_lo == $past(in[7:0]));
  cover property (past_valid && in[15:8] == $past(in[15:8]) && in[7:0] != $past(in[7:0])
                  ##1 out_hi == $past(in[15:8]) && out_lo == $past(in[7:0]));

endmodule