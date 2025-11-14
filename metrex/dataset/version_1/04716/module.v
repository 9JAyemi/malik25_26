module glitch_filter (
  input in,
  input clk,
  output reg out
);

parameter n = 4; // number of clock cycles for glitch filter

reg [n-1:0] shift_reg;
reg [n-1:0] prev_values;

always @(posedge clk) begin
  shift_reg <= {shift_reg[n-2:0], in};
  prev_values <= {prev_values[n-2:0], shift_reg[0]};
end

always @(*) begin
  out = (shift_reg == {n{in}}) ? in : prev_values[0];
end

endmodule