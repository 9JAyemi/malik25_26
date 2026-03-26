module johnson_counter #(
  parameter m = 4 // number of output signals
)(
  input clk,
  output [m-1:0] out
);


reg [m-1:0] shift_reg;
assign out = shift_reg;

always @(posedge clk) begin
  shift_reg <= {shift_reg[m-2:0], shift_reg[m-1]};
end

endmodule