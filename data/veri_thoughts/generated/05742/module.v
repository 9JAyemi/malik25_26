module pin_control(
  input clk,
  input reset,
  input [17:0] data,
  output [17:0] out_data
);

reg [17:0] shift_reg;

always @(posedge clk) begin
  if (reset) begin
    shift_reg <= 18'b0;
  end else begin
    shift_reg <= {shift_reg[16:0], data[0]};
  end
end

assign out_data = shift_reg;

endmodule