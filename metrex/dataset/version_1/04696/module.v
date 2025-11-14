module digital_clock (
  input clk_in,
  input rst,
  input en,
  output reg clk_out,
  output reg clk_out_b
);

reg [2:0] counter;

always @(posedge clk_in or posedge rst) begin
  if (rst) begin
    counter <= 3'b0;
    clk_out <= 1'b0;
    clk_out_b <= 1'b0;
  end else begin
    if (en) begin
      counter <= counter + 1;
      if (counter == 3'b011) begin
        clk_out <= ~clk_out;
      end
      if (counter == 3'b010) begin
        clk_out_b <= ~clk_out_b;
      end
    end
  end
end

endmodule