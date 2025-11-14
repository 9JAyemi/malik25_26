module mem_wb_reg
#(
   parameter DATA_WIDTH = 32,
   parameter INSTRUCTION_WIDTH = 32,
   parameter REG_ADDR_WIDTH = 5
  )
(
   input clk,
   input rst_n,
   input en,
   input write_back_mux_sel_in,
   input [DATA_WIDTH-1:0] alu_data_in,
   input [DATA_WIDTH-1:0] hi_data_in,
input [REG_ADDR_WIDTH-1:0] reg_a_wr_addr_in,
   input [REG_ADDR_WIDTH-1:0] reg_b_wr_addr_in,
   input reg_a_wr_en_in,
   input reg_b_wr_en_in,
   input [INSTRUCTION_WIDTH-1:0] instruction_in,

   output reg write_back_mux_sel_out,
   output reg [DATA_WIDTH-1:0] alu_data_out,
   output reg [DATA_WIDTH-1:0] hi_data_out,
output reg [REG_ADDR_WIDTH-1:0] reg_a_wr_addr_out,
   output reg [REG_ADDR_WIDTH-1:0] reg_b_wr_addr_out,
   output reg reg_a_wr_en_out,
   output reg reg_b_wr_en_out,
   output reg [INSTRUCTION_WIDTH-1:0] instruction_out
);



always@(posedge clk or negedge rst_n) begin
   if(~rst_n) begin
      write_back_mux_sel_out <= 0;
      alu_data_out <= 0;
      hi_data_out <= 0;
reg_a_wr_addr_out <= 0;
      reg_b_wr_addr_out <= 0;
      reg_a_wr_en_out <= 0;
      reg_b_wr_en_out <= 0;
      instruction_out <= 0;
   end
   else if(en) begin
      write_back_mux_sel_out <= write_back_mux_sel_in;
      alu_data_out <= alu_data_in;
      hi_data_out <= hi_data_in;
reg_a_wr_addr_out <= reg_a_wr_addr_in;
      reg_b_wr_addr_out <= reg_b_wr_addr_in;
      reg_a_wr_en_out <= reg_a_wr_en_in;
      reg_b_wr_en_out <= reg_b_wr_en_in;
      instruction_out <= instruction_in;
   end
end

endmodule
