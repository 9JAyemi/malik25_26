module frequency_divider (
  input clk_in,
  input rst,
  output reg clk_out
);

parameter div = 10;

reg [31:0] count;

always @(posedge clk_in or posedge rst) begin
  if (rst) begin
    count <= 0;
    clk_out <= 0;
  end else begin
    count <= count + 1;
    if (count == div - 1) begin
      count <= 0;
      clk_out <= ~clk_out;
    end
  end
end

endmodule