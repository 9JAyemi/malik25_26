// SVA for wb_stream_writer_ctrl
module wb_stream_writer_ctrl_sva
  #(parameter WB_AW = 32,
    parameter WB_DW = 32,
    parameter FIFO_AW = 0,
    parameter MAX_BURST_LEN = 0)
(
   input                  wb_clk_i,
   input                  wb_rst_i,

   // Wishbone
   input  [WB_AW-1:0]     wbm_adr_o,
   input  [WB_DW-1:0]     wbm_dat_o,
   input  [WB_DW/8-1:0]   wbm_sel_o,
   input                  wbm_we_o,
   input                  wbm_cyc_o,
   input                  wbm_stb_o,
   input  [2:0]           wbm_cti_o,
   input  [1:0]           wbm_bte_o,
   input  [WB_DW-1:0]     wbm_dat_i,
   input                  wbm_ack_i,
   input                  wbm_err_i,

   // FIFO
   input  [WB_DW-1:0]     fifo_d,
   input                  fifo_wr,
   input  [FIFO_AW:0]     fifo_cnt,

   // Control
   input                  busy,
   input                  enable,
   input  [WB_DW-1:0]     tx_cnt,
   input  [WB_AW-1:0]     start_adr,
   input  [WB_AW-1:0]     buf_size,
   input  [WB_AW-1:0]     burst_size,

   // Internal DUT signals (via bind)
   input                  active,
   input                  last_adr,
   input  [1:0]           state,
   input                  burst_end,
   input                  fifo_ready
);

  localparam S_IDLE   = 2'd0;
  localparam S_ACTIVE = 2'd1;

  default clocking cb @(posedge wb_clk_i); endclocking
  default disable iff (wb_rst_i);

  // Basic tie-offs and bus invariants
  assert property (wbm_we_o == 1'b0);
  assert property (wbm_sel_o == {WB_DW/8{1'b1}});
  assert property (wbm_bte_o == 2'b00);
  assert property (wbm_dat_o == '0);

  // Valid/ready and handshake
  assert property (active |-> (wbm_cyc_o && wbm_stb_o));
  assert property (!active |-> (!wbm_cyc_o && !wbm_stb_o && wbm_cti_o==3'b000));
  assert property (wbm_ack_i |-> active && wbm_cyc_o && wbm_stb_o && !wbm_err_i);

  // CTI behavior
  assert property (active && !burst_end |-> wbm_cti_o == 3'b010);
  assert property (active &&  burst_end |-> wbm_cti_o == 3'b111);

  // FIFO side effects
  assert property (fifo_wr == wbm_ack_i);
  assert property (fifo_d  == wbm_dat_i);

  // Address function and alignment
  assert property (wbm_adr_o == start_adr + (tx_cnt<<2));
  assert property (wbm_adr_o[1:0] == start_adr[1:0]);

  // Address and counter progression on ACK
  assert property (wbm_ack_i && !last_adr |=> wbm_adr_o == $past(wbm_adr_o) + 4);
  assert property (wbm_ack_i &&  last_adr |=> wbm_adr_o == start_adr);

  assert property (!wbm_ack_i |=> tx_cnt == $past(tx_cnt));
  assert property (wbm_ack_i && !last_adr |=> tx_cnt == $past(tx_cnt) + 1);
  assert property (wbm_ack_i &&  last_adr |=> tx_cnt == '0);

  // FSM activation/deactivation rules
  assert property ($rose(active) |-> $past(state==S_IDLE && busy && fifo_ready));
  assert property ($fell(active) |-> $past(burst_end && wbm_ack_i));

  // IDLE -> ACTIVE when allowed
  assert property (state==S_IDLE && busy && fifo_ready |=> state==S_ACTIVE);

  // Busy set/clear rules
  assert property ($rose(busy) |-> $past(enable) && $past(state==S_IDLE));
  assert property (busy && !($past(state==S_ACTIVE && burst_end && wbm_ack_i && last_adr)) |=> busy);

  // Reset post-conditions
  assert property ($rose(wb_rst_i) |=> state==S_IDLE && tx_cnt=='0 && busy==1'b0
                                     && !wbm_cyc_o && !wbm_stb_o && wbm_cti_o==3'b000);

  // No X on primary bus outputs
  assert property (!$isunknown({wbm_cyc_o, wbm_stb_o, wbm_cti_o, wbm_bte_o, wbm_we_o, wbm_sel_o, wbm_adr_o}));

  // Gating against FIFO overflow on activation
  assert property ($rose(active) |-> fifo_ready);

  // Coverage
  cover property ($rose(active) ##[1:$] (burst_end && wbm_ack_i) ##1 $fell(active));
  cover property (wbm_ack_i && last_adr ##1 tx_cnt=='0);
  cover property ($rose(active) && burst_end ##1 wbm_ack_i ##1 $fell(active)); // single-beat burst
  cover property ($rose(busy) ##[1:$] $rose(active) ##[1:$]
                  (burst_end && wbm_ack_i && last_adr) ##1 !busy);

endmodule

// Bind into DUT
bind wb_stream_writer_ctrl
  wb_stream_writer_ctrl_sva #(.WB_AW(WB_AW), .WB_DW(WB_DW), .FIFO_AW(FIFO_AW), .MAX_BURST_LEN(MAX_BURST_LEN))
  wb_stream_writer_ctrl_sva_i (.*);