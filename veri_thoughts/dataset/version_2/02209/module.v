module register (
  input clk,
  input reset,
  input enable,
  input [31:0] data_in,
  output reg [31:0] data_out
);

  always @(posedge clk) begin
    if (reset) begin
      data_out <= 0;
    end else if (enable) begin
      data_out <= data_in;
    end else begin
      data_out <= data_out;
    end
  end

endmodule