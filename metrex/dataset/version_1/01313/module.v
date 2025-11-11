module shift_register #(
  parameter DATA_WIDTH = 8
) (
  input clk,
  input reset,
  input shift_in,
  output reg shift_out
);

  reg [DATA_WIDTH-1:0] buffer;

  always @(posedge clk) begin
    if (reset) begin
      buffer <= 0;
      shift_out <= 0;
    end else begin
      buffer <= {shift_in, buffer[DATA_WIDTH-1:1]};
      shift_out <= buffer[0];
    end
  end

endmodule