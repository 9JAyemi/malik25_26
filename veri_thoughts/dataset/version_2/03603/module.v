
module counter (
  input wire clk,
  input wire rst,
  input wire ld,
  input wire [15:0] d,
  output reg [15:0] q,
  output reg overflow
);

  always @(posedge clk) begin
    if (rst) begin
      q <= 0;
      overflow <= 0;
    end else if (ld) begin
      q <= d;
      overflow <= 0;
    end else if (q == 16'hFFFF) begin
      q <= 0;
      overflow <= 1;
    end else begin
      q <= q + 1'b1;
      overflow <= 0;
    end
  end

endmodule