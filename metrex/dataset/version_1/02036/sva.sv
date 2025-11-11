// SVA for usb_crc5
`ifndef USB_CRC5_SVA_SV
`define USB_CRC5_SVA_SV

module usb_crc5_sva;

  // Access to DUT signals via bind scope
  // clk, rst, data_in, crc_en, crc_out, lfsr_q, lfsr_c

  default clocking cb @(posedge clk); endclocking

  function automatic [4:0] next_crc5(input [4:0] q, input [10:0] d);
    next_crc5[0] = q[0] ^ q[3] ^ q[4] ^ d[0] ^ d[3] ^ d[5] ^ d[6] ^ d[9] ^ d[10];
    next_crc5[1] = q[0] ^ q[1] ^ q[4] ^ d[1] ^ d[4] ^ d[6] ^ d[7] ^ d[10];
    next_crc5[2] = q[0] ^ q[1] ^ q[2] ^ q[3] ^ q[4] ^ d[0] ^ d[2] ^ d[3] ^ d[6] ^ d[7] ^ d[8] ^ d[9] ^ d[10];
    next_crc5[3] = q[1] ^ q[2] ^ q[3] ^ q[4] ^ d[1] ^ d[3] ^ d[4] ^ d[7] ^ d[8] ^ d[9] ^ d[10];
    next_crc5[4] = q[2] ^ q[3] ^ q[4] ^ d[2] ^ d[4] ^ d[5] ^ d[8] ^ d[9] ^ d[10];
  endfunction

  // Output mapping
  a_out_map:                assert property (crc_out == ~lfsr_q);

  // Combinational next-state correctness
  a_comb_eq:                assert property (lfsr_c == next_crc5(lfsr_q, data_in));

  // Asynchronous reset behavior
  a_async_rst_edge:         assert property (@(posedge rst) lfsr_q == 5'h1F);
  a_rst_while_high:         assert property (@(posedge clk) rst |-> (lfsr_q == 5'h1F) && (crc_out == 5'h00));

  // No X/Z during normal operation
  a_no_x:                   assert property (@(posedge clk) !rst |-> !$isunknown({crc_en, data_in, lfsr_q, crc_out, lfsr_c}));

  // Hold when disabled
  a_hold_when_disabled:     assert property (@(posedge clk) !rst && $past(!rst) && $past(!crc_en) |-> lfsr_q == $past(lfsr_q));

  // Update when enabled (cycle-accurate next-state)
  a_update_when_enabled:    assert property (@(posedge clk) !rst && $past(!rst) && $past(crc_en) |-> lfsr_q == next_crc5($past(lfsr_q), $past(data_in)));

  // Lightweight functional coverage
  c_reset_seen:             cover  property (@(posedge rst) 1);
  c_enable_seen:            cover  property (@(posedge clk) !rst ##1 $rose(crc_en));
  c_hold_seen:              cover  property (@(posedge clk) !rst ##1 !crc_en ##1 !crc_en);

  genvar i;
  generate
    for (i=0; i<5; i++) begin : gen_cov_bits
      c_bit_toggle_10: cover property (@(posedge clk) !rst && $past(!rst) &&  $past(lfsr_q[i]) && !lfsr_q[i]);
      c_bit_toggle_01: cover property (@(posedge clk) !rst && $past(!rst) && !$past(lfsr_q[i]) &&  lfsr_q[i]);
    end
  endgenerate

endmodule

bind usb_crc5 usb_crc5_sva sva_usb_crc5();

`endif