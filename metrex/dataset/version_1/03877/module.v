module shift_register #(
  parameter n = 4, // number of input signals
  parameter m = 4 // number of output signals
)(
  input [n-1:0] data_in,
  input clk,
  input reset,
  input shift,
  output [m-1:0] data_out
);

parameter width = 8; // width of shift register in bits

reg [width-1:0] shift_reg;

always @(posedge clk) begin
  if (reset) begin
    shift_reg <= 0;
  end else if (shift) begin
    if (shift == 1'b1) begin // shift right
      shift_reg <= {1'b0, shift_reg[width-1:1]};
    end else begin // shift left
      shift_reg <= {shift_reg[width-2:0], 1'b0};
    end
  end else begin
    shift_reg <= data_in;
  end
end

assign data_out = shift_reg;

endmodule