module simple_counter(
  input clk,
  input rst_n,
  input en,
  output reg [3:0] count
);

  always @(posedge clk) begin
    if (!rst_n) begin
      count <= 4'b0;
    end else if (en) begin
      count <= (count == 4'b1111) ? 4'b0 : count + 1'b1;
    end
  end

endmodule