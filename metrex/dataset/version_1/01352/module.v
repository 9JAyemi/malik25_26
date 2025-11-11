


module wb_drp #
(
    parameter ADDR_WIDTH = 16
)
(
    input  wire                    clk,
    input  wire                    rst,

    
    input  wire [ADDR_WIDTH-1:0]   wb_adr_i,   input  wire [15:0]             wb_dat_i,   output wire [15:0]             wb_dat_o,   input  wire                    wb_we_i,    input  wire                    wb_stb_i,   output wire                    wb_ack_o,   input  wire                    wb_cyc_i,   
    output wire [ADDR_WIDTH-1:0]   drp_addr,
    output wire [15:0]             drp_do,
    input  wire [15:0]             drp_di,
    output wire                    drp_en,
    output wire                    drp_we,
    input  wire                    drp_rdy
);

reg cycle = 1'b0;

assign drp_addr = wb_adr_i;
assign drp_do = wb_dat_i;
assign wb_dat_o = drp_di;
assign drp_en = wb_cyc_i & wb_stb_i & ~cycle;
assign drp_we = wb_cyc_i & wb_stb_i & wb_we_i & ~cycle;
assign wb_ack_o = drp_rdy;

always @(posedge clk) begin
    cycle <= wb_cyc_i & wb_stb_i & ~drp_rdy;

    if (rst) begin
        cycle <= 1'b0;
    end
end

endmodule
