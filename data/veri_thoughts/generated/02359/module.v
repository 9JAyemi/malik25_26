
module counter (
  input clk,
  input ce,
  input clr,
  output reg [7:0] count
);

  always @(posedge clk) begin
    if (clr == 1'b1) begin
      count <= 8'b0;
    end else if (ce == 1'b1) begin
      count <= count + 1;
    end
  end

endmodule