// SVA for wb_mux_2
module wb_mux_2_sva #
(
  parameter DATA_WIDTH   = 32,
  parameter ADDR_WIDTH   = 32,
  parameter SELECT_WIDTH = (DATA_WIDTH/8)
)
(
  input  logic                    clk,
  input  logic                    rst,

  input  logic [ADDR_WIDTH-1:0]   wbm_adr_i,
  input  logic [DATA_WIDTH-1:0]   wbm_dat_i,
  input  logic                    wbm_we_i,
  input  logic [SELECT_WIDTH-1:0] wbm_sel_i,
  input  logic                    wbm_stb_i,
  input  logic                    wbm_cyc_i,
  input  logic [DATA_WIDTH-1:0]   wbm_dat_o,
  input  logic                    wbm_ack_o,
  input  logic                    wbm_err_o,
  input  logic                    wbm_rty_o,

  input  logic [ADDR_WIDTH-1:0]   wbs0_adr_o,
  input  logic [DATA_WIDTH-1:0]   wbs0_dat_i,
  input  logic [DATA_WIDTH-1:0]   wbs0_dat_o,
  input  logic                    wbs0_we_o,
  input  logic [SELECT_WIDTH-1:0] wbs0_sel_o,
  input  logic                    wbs0_stb_o,
  input  logic                    wbs0_ack_i,
  input  logic                    wbs0_err_i,
  input  logic                    wbs0_rty_i,
  input  logic                    wbs0_cyc_o,

  input  logic [ADDR_WIDTH-1:0]   wbs0_addr,
  input  logic [ADDR_WIDTH-1:0]   wbs0_addr_msk,

  input  logic [ADDR_WIDTH-1:0]   wbs1_adr_o,
  input  logic [DATA_WIDTH-1:0]   wbs1_dat_i,
  input  logic [DATA_WIDTH-1:0]   wbs1_dat_o,
  input  logic                    wbs1_we_o,
  input  logic [SELECT_WIDTH-1:0] wbs1_sel_o,
  input  logic                    wbs1_stb_o,
  input  logic                    wbs1_ack_i,
  input  logic                    wbs1_err_i,
  input  logic                    wbs1_rty_i,
  input  logic                    wbs1_cyc_o,

  input  logic [ADDR_WIDTH-1:0]   wbs1_addr,
  input  logic [ADDR_WIDTH-1:0]   wbs1_addr_msk
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Local decodes (replicate DUT logic)
  logic match0, match1, mcycle;
  always_comb begin
    match0  = ~|((wbm_adr_i ^ wbs0_addr) & wbs0_addr_msk);
    match1  = ~|((wbm_adr_i ^ wbs1_addr) & wbs1_addr_msk);
    mcycle  = wbm_cyc_i & wbm_stb_i;
  end

  // Structural pass-through checks
  assert property (wbs0_adr_o == wbm_adr_i);
  assert property (wbs1_adr_o == wbm_adr_i);
  assert property (wbs0_dat_o == wbm_dat_i);
  assert property (wbs1_dat_o == wbm_dat_i);
  assert property (wbs0_sel_o == wbm_sel_i);
  assert property (wbs1_sel_o == wbm_sel_i);
  assert property (wbs0_stb_o |-> (wbs0_we_o == wbm_we_i));
  assert property (wbs1_stb_o |-> (wbs1_we_o == wbm_we_i));

  // Basic Wishbone protocol relations at the mux outputs
  assert property (!(wbs0_cyc_o && wbs1_cyc_o));
  assert property (!(wbs0_stb_o && wbs1_stb_o));
  assert property (wbs0_stb_o |-> wbs0_cyc_o);
  assert property (wbs1_stb_o |-> wbs1_cyc_o);

  // Selection behavior and priority (0 over 1)
  assert property ((mcycle && match0) |-> (wbs0_cyc_o==wbm_cyc_i && wbs0_stb_o==wbm_stb_i && !wbs1_cyc_o && !wbs1_stb_o));
  assert property ((mcycle && !match0 && match1) |-> (wbs1_cyc_o==wbm_cyc_i && wbs1_stb_o==wbm_stb_i && !wbs0_cyc_o && !wbs0_stb_o));
  assert property ((mcycle && !match0 && !match1) |-> (!wbs0_cyc_o && !wbs0_stb_o && !wbs1_cyc_o && !wbs1_stb_o && wbm_err_o));

  // Data mux correctness
  assert property (((wbs0_cyc_o || wbs0_stb_o)) |-> (wbm_dat_o == wbs0_dat_i));
  assert property (((wbs1_cyc_o || wbs1_stb_o)) |-> (wbm_dat_o == wbs1_dat_i));
  assert property ((!(wbs0_cyc_o || wbs0_stb_o || wbs1_cyc_o || wbs1_stb_o)) |-> (wbm_dat_o == '0));

  // Response aggregation
  assert property (wbm_ack_o == (wbs0_ack_i | wbs1_ack_i));
  assert property (wbm_rty_o == (wbs0_rty_i | wbs1_rty_i));

  // Error aggregation with decode
  assert property ((mcycle && match0)              |-> (wbm_err_o == wbs0_err_i));
  assert property ((mcycle && !match0 && match1)   |-> (wbm_err_o == wbs1_err_i));
  assert property ((mcycle && !match0 && !match1)  |-> (wbm_err_o));
  assert property ((!mcycle)                       |-> (wbm_err_o == (wbs0_err_i | wbs1_err_i)));

  // Environment/handshake sanity (ensures spurious slave responses are caught)
  assert property ((wbs0_ack_i || wbs0_err_i || wbs0_rty_i) |-> (wbs0_cyc_o && wbs0_stb_o));
  assert property ((wbs1_ack_i || wbs1_err_i || wbs1_rty_i) |-> (wbs1_cyc_o && wbs1_stb_o));
  assert property ((wbm_ack_o || wbm_err_o || wbm_rty_o)    |-> mcycle);

  // Functional coverage
  cover property (mcycle && match0 && !wbm_we_i ##1 wbs0_ack_i);
  cover property (mcycle && match0 &&  wbm_we_i ##1 wbs0_ack_i);
  cover property (mcycle && !match0 && match1 && !wbm_we_i ##1 wbs1_ack_i);
  cover property (mcycle && !match0 && match1 &&  wbm_we_i ##1 wbs1_ack_i);
  cover property (mcycle && match0 && match1 && wbs0_stb_o && !wbs1_stb_o);
  cover property (mcycle && !match0 && !match1 ##1 wbm_err_o);

endmodule

// Bind into DUT
bind wb_mux_2 wb_mux_2_sva #(.DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .SELECT_WIDTH(SELECT_WIDTH)) wb_mux_2_sva_i (.*);