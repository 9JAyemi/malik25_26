module write_back
#(
   parameter DATA_WIDTH = 32,
   parameter REG_ADDR_WIDTH = 5
 )
(
   input [DATA_WIDTH-1:0] mem_data_in,
   input [DATA_WIDTH-1:0] alu_data_in,
   input [DATA_WIDTH-1:0] hi_data_in,
input [REG_ADDR_WIDTH-1:0] reg_a_wr_addr_in,
   input [REG_ADDR_WIDTH-1:0] reg_b_wr_addr_in,
   input reg_a_wr_en_in,
   input reg_b_wr_en_in,
   input write_back_mux_sel,

   output [REG_ADDR_WIDTH-1:0] reg_a_wr_addr_out,
   output [REG_ADDR_WIDTH-1:0] reg_b_wr_addr_out,
   output [DATA_WIDTH-1:0] reg_a_wr_data_out,
   output [DATA_WIDTH-1:0] reg_b_wr_data_out,
   output reg_a_wr_en_out,
   output reg_b_wr_en_out
);

assign reg_a_wr_data_out = write_back_mux_sel?mem_data_in:alu_data_in;
assign reg_b_wr_data_out = hi_data_in;
assign reg_a_wr_en_out = reg_a_wr_en_in;
assign reg_b_wr_en_out = reg_b_wr_en_in;
assign reg_a_wr_addr_out = reg_a_wr_addr_in;
assign reg_b_wr_addr_out = reg_b_wr_addr_in;

endmodule
