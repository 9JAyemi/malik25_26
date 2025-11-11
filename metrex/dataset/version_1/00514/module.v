module fifo #(
  parameter WIDTH = 8
)
(
  input clk,
  input reset,
  input wr_en,
  input rd_en,
  input [WIDTH-1:0] din,
  output reg [WIDTH-1:0] dout,
  output reg full,
  output reg empty
);

  reg [WIDTH-1:0] buffer [0:15];
  reg [4:0] head;
  reg [4:0] tail;
  wire [4:0] count = head - tail;

  always @(posedge clk) begin
    if (reset) begin
      head <= 0;
      tail <= 0;
    end else begin
      if (wr_en && !full) begin
        buffer[head] <= din;
        head <= head + 1;
      end
      if (rd_en && !empty) begin
        dout <= buffer[tail];
        tail <= tail + 1;
      end
    end
  end

  always @* begin
    full = (count == 16);
    empty = (count == 0);
  end

endmodule