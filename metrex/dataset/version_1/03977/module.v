
module fifo_generator (
  input clk,
  input [4:0] din,
  input s_aclk,
  input rst,
  input rd_en,
  input wr_en,
  input s_aresetn,
  output reg [4:0] dout,
  output empty,
  output full
);

  // Define parameters
  parameter WIDTH = 5;
  parameter DEPTH = 1024;
  parameter ADDR_WIDTH = $clog2(DEPTH);

  // Define registers
  reg [ADDR_WIDTH-1:0] wptr = 0;
  reg [ADDR_WIDTH-1:0] rptr = 0;
  reg [WIDTH-1:0] mem [0:DEPTH-1];

  // Define wires
  reg [ADDR_WIDTH-1:0] next_wptr;
  reg [ADDR_WIDTH-1:0] next_rptr;
  
  // Define slower clock domain registers
  reg [31:0] slow_cnt = 0;
  reg [31:0] slow_wr_cnt = 0;
  reg [31:0] slow_rd_cnt = 0;

  // Define slower clock domain wires
  wire slow_wr_en;
  wire slow_rd_en;

  // Synchronize signals to the slower clock domain
  always @(posedge s_aclk) begin
    if (~s_aresetn) begin
      slow_cnt <= 0;
      slow_wr_cnt <= 0;
      slow_rd_cnt <= 0;
    end else begin
      slow_cnt <= slow_cnt + 1;
      slow_wr_cnt <= slow_wr_cnt + wr_en;
      slow_rd_cnt <= slow_rd_cnt + rd_en;
    end
  end

  // Generate slower clock domain signals
  assign slow_wr_en = (slow_wr_cnt >= (DEPTH/2)) ? 1'b0 : 1'b1;
  assign slow_rd_en = (slow_rd_cnt >= (DEPTH/2)) ? 1'b0 : 1'b1;

  // Synchronize read and write pointers to the slower clock domain
  always @(posedge s_aclk) begin
    if (~s_aresetn) begin
      next_wptr <= 0;
      next_rptr <= 0;
    end else if (slow_cnt == 0) begin
      next_wptr <= (slow_wr_en && wr_en) ? wptr + 1'b1 : wptr;
      next_rptr <= (slow_rd_en && rd_en) ? rptr + 1'b1 : rptr;
    end else begin
      next_wptr <= wptr;
      next_rptr <= rptr;
    end
  end

  // Update read and write pointers
  always @(posedge clk) begin
    if (~rst) begin
      wptr <= 0;
      rptr <= 0;
    end else begin
      wptr <= next_wptr;
      rptr <= next_rptr;
    end
  end

  // Write data to memory
  always @(posedge clk) begin
    if (~rst && wr_en) begin
      mem[wptr] <= din;
    end
  end

  // Read data from memory
  always @(posedge clk) begin
    if (~rst && rd_en) begin
      dout <= mem[rptr];
    end
  end

  // Check if FIFO is empty or full
  assign empty = (wptr == rptr) ? 1'b1 : 1'b0;
  assign full = ((wptr+1'b1) == rptr) ? 1'b1 : 1'b0;

endmodule