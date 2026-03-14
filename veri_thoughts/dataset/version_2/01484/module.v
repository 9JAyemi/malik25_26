
module counter(
  input clk,
  input reset,
  output reg [3:0] out
);

  // Combinational always block
  always @ (posedge clk or posedge reset) begin
    if (reset) begin
      out <= 4'b0000;
    end else begin
      out <= out + 1;
    end
  end

endmodule