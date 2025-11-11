// SVA for block_mem: concise, quality-focused checks and coverage

// Bind module
module block_mem_sva (
  input logic              clk,
  input logic [12:0]       addr,
  input logic [9:0]        din,
  input logic              we,
  input logic [9:0]        dout,
  input logic [7:0]        douta10,
  input logic              douta11,
  input logic [13:0]       addra,
  input logic [8:0]        dina,
  input logic              wea
);
  default clocking cb @ (posedge clk); endclocking

  // Structural connectivity/width mapping
  a_addra_map: assert property (addra == {1'b0, addr});
  a_dina_map:  assert property (dina  == din[8:0]);
  a_we_map:    assert property (wea   == we);

  // No-X on key paths at sample points
  a_no_x_in:       assert property (!$isunknown({addr, din, we}));
  a_no_x_mem_out:  assert property (!$isunknown({douta10, douta11}));

  // Registered output must equal zero-extended douta10 (douta11 has no effect)
  a_dout_eq:           assert property (1'b1 |-> ##1 (dout == {2'b00, $past(douta10)}));
  a_dout_upper_zero:   assert property (1'b1 |-> ##1 (dout[9:8] == 2'b00));

  // Explicitly prove douta11 has no functional impact on dout when data is stable
  a_flag_no_effect: assert property ($changed(douta11) && $stable(douta10) |-> ##1 $stable(dout));

  // Prove din[9] is ignored by dina (only when lower bits are stable)
  a_din_msb_ignored: assert property ($changed(din[9]) && $stable(din[8:0]) |-> $stable(dina));

  // Lightweight coverage
  c_we_edge:          cover property ($rose(we) or $fell(we));
  c_addr_toggle:      cover property ($changed(addr));
  c_addr_msb0:        cover property (!addr[12]);
  c_addr_msb1:        cover property ( addr[12]);
  c_din_msb_toggle:   cover property ($changed(din[9]) && $stable(din[8:0]));
  c_douta11_hi:       cover property ($rose(douta11));
  c_douta11_lo:       cover property ($fell(douta11));
  c_dout_nonzero:     cover property (##1 (dout != 10'h000));

endmodule

// Bind into DUT
bind block_mem block_mem_sva u_block_mem_sva (
  .clk    (clk),
  .addr   (addr),
  .din    (din),
  .we     (we),
  .dout   (dout),
  .douta10(douta10),
  .douta11(douta11),
  .addra  (addra),
  .dina   (dina),
  .wea    (wea)
);