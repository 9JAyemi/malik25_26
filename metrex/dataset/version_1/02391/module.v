module fifo(
  input clk,
  input rst,
  input [7:0] din,
  input wr_en,
  input rd_en,
  output reg [7:0] dout,
  output reg full,
  output reg empty
);

parameter DEPTH = 16;

reg [7:0] mem [0:DEPTH-1];
reg [3:0] wr_ptr = 0;
reg [3:0] rd_ptr = 0;
reg [3:0] count = 0;

always @(posedge clk or posedge rst) begin
  if (rst) begin
    wr_ptr <= 0;
    rd_ptr <= 0;
    count <= 0;
  end else begin
    if (wr_en && !full) begin
      mem[wr_ptr] <= din;
      wr_ptr <= wr_ptr + 1;
      count <= count + 1;
    end
    if (rd_en && !empty) begin
      dout <= mem[rd_ptr];
      rd_ptr <= rd_ptr + 1;
      count <= count - 1;
    end
  end
end

always @* begin
  full = (count == DEPTH);
  empty = (count == 0);
end

endmodule