module binary_counter (
  input clk, // input clock
  input reset, // asynchronous reset
  input enable, // enable counter
  output reg [3:0] Q // output binary count
);

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      Q <= 4'b0;
    end else if (enable) begin
      Q <= Q + 1;
    end
  end

endmodule