// SVA for wb_drp: concise, high-signal-coverage, protocol-centric
// Bindable checker with minimal environment assumptions

`ifndef WB_DRP_SVA_SV
`define WB_DRP_SVA_SV

module wb_drp_sva #(parameter ADDR_WIDTH = 16) (
  input  logic                     clk,
  input  logic                     rst,

  // Wishbone side
  input  logic [ADDR_WIDTH-1:0]    wb_adr_i,
  input  logic [15:0]              wb_dat_i,
  input  logic [15:0]              wb_dat_o,
  input  logic                     wb_we_i,
  input  logic                     wb_stb_i,
  input  logic                     wb_ack_o,
  input  logic                     wb_cyc_i,

  // DRP side
  input  logic [ADDR_WIDTH-1:0]    drp_addr,
  input  logic [15:0]              drp_do,
  input  logic [15:0]              drp_di,
  input  logic                     drp_en,
  input  logic                     drp_we,
  input  logic                     drp_rdy,

  // Internal
  input  logic                     cycle
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Combinational pass-throughs
  assert property (drp_addr == wb_adr_i);
  assert property (drp_do   == wb_dat_i);
  assert property (wb_dat_o == drp_di);

  // Handshake/controls mapping
  assert property (wb_ack_o == drp_rdy);
  assert property (drp_en   == (wb_cyc_i && wb_stb_i && !cycle));
  assert property (drp_we   == (drp_en && wb_we_i));

  // Basic protocol sanity
  assert property (drp_en |-> (wb_cyc_i && wb_stb_i));
  assert property (drp_we |-> (drp_en && wb_we_i));
  assert property (cycle  |-> (!drp_en && !drp_we)); // busy blocks new enables

  // Registered busy flag relation to inputs
  assert property (cycle == $past(wb_cyc_i && wb_stb_i && !drp_rdy, 1, rst));
  assert property (drp_rdy |=> !cycle);
  assert property ((drp_en && !drp_rdy) |=> !drp_en); // single-shot enable when wait state

  // Wishbone-friendly: no ACK when CYC is low (flag environment/design issues)
  assert property (wb_ack_o |-> wb_cyc_i);

  // No X/Z on key outputs
  assert property (!$isunknown({drp_en, drp_we, wb_ack_o, drp_addr, drp_do, wb_dat_o}));

  // Coverage: read/write, wait/zero-wait, back-to-back, and abort
  cover property (drp_en &&  wb_we_i && !drp_rdy ##[1:8] wb_ack_o); // write with wait
  cover property (drp_en && !wb_we_i && !drp_rdy ##[1:8] wb_ack_o); // read with wait
  cover property (drp_en &&  wb_we_i &&  drp_rdy);                  // zero-wait write
  cover property (drp_en && !wb_we_i &&  drp_rdy);                  // zero-wait read
  cover property (wb_ack_o ##1 drp_en);                              // back-to-back ops
  cover property (drp_en && !drp_rdy ##[1:8] (!wb_cyc_i || !wb_stb_i) && !wb_ack_o); // abort before ACK

endmodule

// Bind into the DUT (captures internal 'cycle' via explicit connection)
bind wb_drp wb_drp_sva #(.ADDR_WIDTH(ADDR_WIDTH)) wb_drp_sva_i (
  .clk(clk),
  .rst(rst),
  .wb_adr_i(wb_adr_i),
  .wb_dat_i(wb_dat_i),
  .wb_dat_o(wb_dat_o),
  .wb_we_i(wb_we_i),
  .wb_stb_i(wb_stb_i),
  .wb_ack_o(wb_ack_o),
  .wb_cyc_i(wb_cyc_i),
  .drp_addr(drp_addr),
  .drp_do(drp_do),
  .drp_di(drp_di),
  .drp_en(drp_en),
  .drp_we(drp_we),
  .drp_rdy(drp_rdy),
  .cycle(cycle)
);

`endif