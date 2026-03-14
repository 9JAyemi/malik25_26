
module accumulator (
  input clk,
  input reset,
  input [7:0] in,
  output [15:0] out
);

  reg [15:0] acc_reg; // register to hold the accumulated sum

  always @(posedge clk) begin
    if (reset) begin
      acc_reg <= 16'd0; // clear the register to zero
    end else begin
      acc_reg <= acc_reg + in; // add the input signal to the register
    end
  end

  assign out = acc_reg; // output the current value of the accumulator register

endmodule