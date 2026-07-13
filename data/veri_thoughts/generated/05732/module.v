module counter #
(
  parameter integer WIDTH = 4
)
(
  input  wire                   clk,
  input  wire                   rst,
  input  wire                   en,
  output reg  [WIDTH-1:0]       count
);

  always @(posedge clk)
  begin
    if (rst) begin
      count <= 0;
    end
    else if (en) begin
      if (count == 2**WIDTH - 1) begin
        count <= 0;
      end
      else begin
        count <= count + 1;
      end
    end
  end

endmodule