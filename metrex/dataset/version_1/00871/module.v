
module fifo_24in_24out_12kb_updn_cntr (
  input clk, E, rd_en, valid_fwft,
  input [23:0] Q,
  output reg [23:0] data_out,
  output reg data_count_out,
  output reg rd_en_out,
  output reg valid_fwft_out,
  output reg [23:0] Q_out
);
  localparam WIDTH = 24;
  localparam DEPTH = 512;
  localparam ADDR_WIDTH = $clog2(DEPTH);
  localparam MEM_SIZE = 1 << ADDR_WIDTH;
  reg [23:0] mem [0:MEM_SIZE-1];
  reg [ADDR_WIDTH-1:0] wr_ptr;
  reg [ADDR_WIDTH-1:0] rd_ptr;
  reg [ADDR_WIDTH:0] data_count;
  wire [ADDR_WIDTH-1:0] next_wr_ptr;
  wire [ADDR_WIDTH-1:0] next_rd_ptr;
  wire [ADDR_WIDTH:0] next_data_count;
  reg [23:0] data_out_internal;
  reg [ADDR_WIDTH:0] data_count_internal;
  reg rd_en_internal;
  reg valid_fwft_internal;
  assign next_wr_ptr = (wr_ptr + 1) % MEM_SIZE;
  assign next_rd_ptr = (rd_ptr + 1) % MEM_SIZE;
  assign next_data_count = data_count + (rd_en_internal ? -1 : 0) + (rd_en ? 1 : 0);
  always @(posedge clk) begin
      wr_ptr <= rd_en_internal ? next_wr_ptr : wr_ptr;
      rd_ptr <= rd_en ? next_rd_ptr : rd_ptr;
      data_count <= next_data_count;
      rd_en_internal <= rd_en;
      valid_fwft_internal <= valid_fwft;
      data_out_internal <= mem[rd_ptr];
      data_count_internal <= next_data_count;
  end
  always @(posedge clk) begin
      data_count_out <= data_count_internal[ADDR_WIDTH-1];
      rd_en_out <= rd_en_internal;
      valid_fwft_out <= valid_fwft_internal;
      Q_out <= Q;
      data_out <= data_out_internal;
  end
  always @(posedge clk) begin
      mem[wr_ptr] <= (rd_en_internal == 1'b0 && rd_en == 1'b0) ? Q : mem[wr_ptr];
  end
endmodule