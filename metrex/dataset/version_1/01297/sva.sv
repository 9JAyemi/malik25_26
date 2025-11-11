// SVA for settings_bus_16LE
module settings_bus_16LE_sva #(parameter AWIDTH=16, RWIDTH=8)
(
  input logic              wb_clk,
  input logic              wb_rst,
  input logic [AWIDTH-1:0] wb_adr_i,
  input logic [15:0]       wb_dat_i,
  input logic              wb_stb_i,
  input logic              wb_we_i,
  input logic              wb_ack_o,
  input logic              strobe,
  input logic [7:0]        addr,
  input logic [31:0]       data
);

  // Reset behavior
  assert property (@(posedge wb_clk) wb_rst |-> (wb_ack_o==0 && strobe==0 && addr==0 && data==0));

  // No Xs after reset deasserted
  assert property (@(posedge wb_clk) disable iff (wb_rst) !$isunknown({wb_ack_o, strobe, addr, data}));

  // ACK generation (single-cycle pulse, depends only on stb)
  assert property (@(posedge wb_clk) disable iff (wb_rst) (wb_stb_i && !wb_ack_o) |=> wb_ack_o);
  assert property (@(posedge wb_clk) disable iff (wb_rst) !wb_stb_i |=> !wb_ack_o);
  assert property (@(posedge wb_clk) disable iff (wb_rst) wb_ack_o |=> !wb_ack_o);

  // Address capture on write, hold otherwise
  assert property (@(posedge wb_clk) disable iff (wb_rst)
                   (wb_we_i && wb_stb_i) |=> addr == $past(wb_adr_i[RWIDTH+1:2]));
  assert property (@(posedge wb_clk) disable iff (wb_rst)
                   !(wb_we_i && wb_stb_i) |=> addr == $past(addr));

  // Data packing on writes, hold otherwise
  assert property (@(posedge wb_clk) disable iff (wb_rst)
                   (wb_we_i && wb_stb_i && !wb_adr_i[1]) |=> (data[15:0]  == $past(wb_dat_i) &&
                                                              data[31:16] == $past(data[31:16])));
  assert property (@(posedge wb_clk) disable iff (wb_rst)
                   (wb_we_i && wb_stb_i && wb_adr_i[1])  |=> (data[31:16] == $past(wb_dat_i) &&
                                                              data[15:0]  == $past(data[15:0])));
  assert property (@(posedge wb_clk) disable iff (wb_rst)
                   !(wb_we_i && wb_stb_i) |=> data == $past(data));

  // Strobe timing: occurs one cycle after a high-half write when ACK can rise
  assert property (@(posedge wb_clk) disable iff (wb_rst)
                   (wb_we_i && wb_stb_i && wb_adr_i[1] && !wb_ack_o) |=> (strobe && wb_ack_o &&
                                                                          addr == $past(wb_adr_i[RWIDTH+1:2])));
  // Strobe cause: must be due to prior high-half write and stb
  assert property (@(posedge wb_clk) disable iff (wb_rst)
                   strobe |-> (wb_ack_o && $past(wb_stb_i && wb_we_i && wb_adr_i[1] && !wb_ack_o)));

  // Functional cover: low-half then high-half to same base addr packs and strobes
  property p_low_then_high_pack_and_strobe;
    logic [7:0]   a;
    logic [15:0]  lo, hi;
    @(posedge wb_clk) disable iff (wb_rst)
      (wb_we_i && wb_stb_i && !wb_adr_i[1], a = wb_adr_i[RWIDTH+1:2], lo = wb_dat_i)
      ##1 (wb_we_i && wb_stb_i && wb_adr_i[1] && wb_adr_i[RWIDTH+1:2]==a && !wb_ack_o, hi = wb_dat_i)
      |=> (strobe && addr==a && data=={hi,lo});
  endproperty
  assert property (p_low_then_high_pack_and_strobe);
  cover  property (p_low_then_high_pack_and_strobe);

  // Cover: high-half-only write still strobes next cycle (when ACK can rise)
  cover property (@(posedge wb_clk) disable iff (wb_rst)
                  (wb_we_i && wb_stb_i && wb_adr_i[1] && !wb_ack_o) ##1 strobe);

  // Cover: continuous stb shows ACK toggling
  cover property (@(posedge wb_clk) disable iff (wb_rst)
                  (wb_stb_i && !wb_ack_o) ##1 wb_ack_o ##1 !wb_ack_o ##1 wb_ack_o);

endmodule

// Bind into the DUT
bind settings_bus_16LE settings_bus_16LE_sva #(.AWIDTH(AWIDTH), .RWIDTH(RWIDTH))
  settings_bus_16LE_sva_i (.*);