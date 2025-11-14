
module wb_adapter (
    input clk,
    input rst,
    input [31:0] wbm_adr_i,
    input [31:0] wbm_dat_i,
    output reg [31:0] wbm_dat_o,
    input wbm_we_i,
    input [3:0] wbm_sel_i,
    input wbm_stb_i,
    output reg wbm_ack_o,
    output reg wbm_err_o,
    output reg wbm_rty_o,
    input [31:0] wbs_dat_i,
    output reg [31:0] wbs_adr_o,
    output reg [31:0] wbs_dat_o,
    output reg wbs_we_o,
    output reg [3:0] wbs_sel_o,
    output reg wbs_stb_o,
    input wbs_ack_i,
    input wbs_err_i,
    input wbs_rty_i,
    output reg wbs_cyc_o
);

always @(posedge clk) begin
    if (rst) begin
        wbm_dat_o <= 32'b0;
        wbm_ack_o <= 1'b0;
        wbm_err_o <= 1'b0;
        wbm_rty_o <= 1'b0;
        wbs_adr_o <= 32'b0;
        wbs_dat_o <= 32'b0;
        wbs_we_o <= 1'b0;
        wbs_sel_o <= 4'b0;
        wbs_stb_o <= 1'b0;
        wbs_cyc_o <= 1'b0;
    end else begin
        wbm_dat_o <= wbs_dat_i;
        wbm_ack_o <= wbs_ack_i;
        wbm_err_o <= wbs_err_i;
        wbm_rty_o <= wbs_rty_i;
        wbs_adr_o <= wbm_adr_i;
        wbs_dat_o <= wbm_dat_i;
        wbs_we_o <= wbm_we_i;
        wbs_sel_o <= wbm_sel_i;
        wbs_stb_o <= wbm_stb_i;
        wbs_cyc_o <= wbm_stb_i;
    end
end

endmodule