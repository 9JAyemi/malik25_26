// SVA checker for crc_ccitt
// Focus: functional equivalence, structural sanity, and concise coverage

module crc_ccitt_sva (
  input  logic        clk,
  input  logic [15:0] data_in,
  input  logic [15:0] shift_reg,
  input  logic [7:0]  crc_reg,
  input  logic [7:0]  crc_out
);

  // Helper: XOR mask accumulated from shift/data bits as per DUT
  function automatic [7:0] xor_mask_from_s(input logic [15:0] s);
    automatic [7:0] acc = 8'h00;
    for (int i = 0; i < 16; i++) begin
      if (s[i]) acc ^= ((i == 15) ? 8'h00 : (8'((15 - i) << 4)));
    end
    return acc;
  endfunction

  function automatic [7:0] pre_xor(input logic [7:0] prev, input logic [15:0] s);
    return prev ^ xor_mask_from_s(s);
  endfunction

  function automatic [7:0] next_crc(input logic [7:0] prev, input logic [15:0] s);
    automatic [7:0] t = pre_xor(prev, s);
    automatic logic [6:0] low7 = t[7] ? ((t[6:0] << 1) ^ 7'h07) : (t[6:0] << 1);
    return {t[7], low7};
  endfunction

  // Basic structural checks
  // shift_reg should equal data_in due to RHS truncation in DUT's combinational assignment
  assert property (@(posedge clk) shift_reg == data_in)
    else $error("shift_reg != data_in (truncation-consistency broken)");

  assert property (@(posedge clk) crc_out == crc_reg)
    else $error("crc_out != crc_reg");

  // No X/Z on key signals at sampling
  assert property (@(posedge clk) !$isunknown({data_in, shift_reg, crc_reg, crc_out}))
    else $error("X/Z detected on interface or internal regs");

  // Glitch-free between clocks (coarse check at negedge)
  assert property (@(negedge clk) $stable(crc_reg) && $stable(crc_out))
    else $error("crc_reg/crc_out changed between clock edges");

  // Golden-step functional check (blocking semantics modeled)
  assert property (@(posedge clk)
      !$isunknown($past(crc_reg)) |-> (crc_reg == next_crc($past(crc_reg), shift_reg)))
    else $error("CRC next-state mismatch vs model");

  // Bit-7 behavior is unaffected by the low-7-bit shift
  assert property (@(posedge clk)
      !$isunknown($past(crc_reg)) |-> (crc_reg[7] == pre_xor($past(crc_reg), shift_reg)[7]))
    else $error("CRC bit[7] mismatch vs pre-shift XOR");

  // Concise functional coverage
  // Exercise both branches of feedback on bit[7] after XOR
  cover property (@(posedge clk) !$isunknown($past(crc_reg)) &&  pre_xor($past(crc_reg), shift_reg)[7]);
  cover property (@(posedge clk) !$isunknown($past(crc_reg)) && !pre_xor($past(crc_reg), shift_reg)[7]);

  // Stimulus extremes and single-bit excitation to hit all masks
  cover property (@(posedge clk) data_in == 16'h0000);
  cover property (@(posedge clk) data_in == 16'hFFFF);
  cover property (@(posedge clk) $onehot(data_in));

  // Output activity
  cover property (@(posedge clk) $changed(crc_out));
  cover property (@(posedge clk) $stable(crc_out));

endmodule

// Bind into DUT
bind crc_ccitt crc_ccitt_sva i_crc_ccitt_sva (
  .clk      (clk),
  .data_in  (data_in),
  .shift_reg(shift_reg),
  .crc_reg  (crc_reg),
  .crc_out  (crc_out)
);