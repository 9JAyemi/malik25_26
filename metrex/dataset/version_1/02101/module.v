


module wb_mux_2 #
(
    parameter DATA_WIDTH = 32,                    parameter ADDR_WIDTH = 32,                    parameter SELECT_WIDTH = (DATA_WIDTH/8)       )
(
    input  wire                    clk,
    input  wire                    rst,

    
    input  wire [ADDR_WIDTH-1:0]   wbm_adr_i,     input  wire [DATA_WIDTH-1:0]   wbm_dat_i,     output wire [DATA_WIDTH-1:0]   wbm_dat_o,     input  wire                    wbm_we_i,      input  wire [SELECT_WIDTH-1:0] wbm_sel_i,     input  wire                    wbm_stb_i,     output wire                    wbm_ack_o,     output wire                    wbm_err_o,     output wire                    wbm_rty_o,     input  wire                    wbm_cyc_i,     
    output wire [ADDR_WIDTH-1:0]   wbs0_adr_o,    input  wire [DATA_WIDTH-1:0]   wbs0_dat_i,    output wire [DATA_WIDTH-1:0]   wbs0_dat_o,    output wire                    wbs0_we_o,     output wire [SELECT_WIDTH-1:0] wbs0_sel_o,    output wire                    wbs0_stb_o,    input  wire                    wbs0_ack_i,    input  wire                    wbs0_err_i,    input  wire                    wbs0_rty_i,    output wire                    wbs0_cyc_o,    
    input  wire [ADDR_WIDTH-1:0]   wbs0_addr,     input  wire [ADDR_WIDTH-1:0]   wbs0_addr_msk, 
    output wire [ADDR_WIDTH-1:0]   wbs1_adr_o,    input  wire [DATA_WIDTH-1:0]   wbs1_dat_i,    output wire [DATA_WIDTH-1:0]   wbs1_dat_o,    output wire                    wbs1_we_o,     output wire [SELECT_WIDTH-1:0] wbs1_sel_o,    output wire                    wbs1_stb_o,    input  wire                    wbs1_ack_i,    input  wire                    wbs1_err_i,    input  wire                    wbs1_rty_i,    output wire                    wbs1_cyc_o,    
    input  wire [ADDR_WIDTH-1:0]   wbs1_addr,     input  wire [ADDR_WIDTH-1:0]   wbs1_addr_msk  );

wire wbs0_match = ~|((wbm_adr_i ^ wbs0_addr) & wbs0_addr_msk);
wire wbs1_match = ~|((wbm_adr_i ^ wbs1_addr) & wbs1_addr_msk);

wire wbs0_sel = wbs0_match;
wire wbs1_sel = wbs1_match & ~(wbs0_match);

wire master_cycle = wbm_cyc_i & wbm_stb_i;

wire select_error = ~(wbs0_sel | wbs1_sel) & master_cycle;

assign wbm_dat_o = wbs0_sel ? wbs0_dat_i :
                   wbs1_sel ? wbs1_dat_i :
                   {DATA_WIDTH{1'b0}};

assign wbm_ack_o = wbs0_ack_i |
                   wbs1_ack_i;

assign wbm_err_o = wbs0_err_i |
                   wbs1_err_i |
                   select_error;

assign wbm_rty_o = wbs0_rty_i |
                   wbs1_rty_i;

assign wbs0_adr_o = wbm_adr_i;
assign wbs0_dat_o = wbm_dat_i;
assign wbs0_we_o = wbm_we_i & wbs0_sel;
assign wbs0_sel_o = wbm_sel_i;
assign wbs0_stb_o = wbm_stb_i & wbs0_sel;
assign wbs0_cyc_o = wbm_cyc_i & wbs0_sel;

assign wbs1_adr_o = wbm_adr_i;
assign wbs1_dat_o = wbm_dat_i;
assign wbs1_we_o = wbm_we_i & wbs1_sel;
assign wbs1_sel_o = wbm_sel_i;
assign wbs1_stb_o = wbm_stb_i & wbs1_sel;
assign wbs1_cyc_o = wbm_cyc_i & wbs1_sel;


endmodule
