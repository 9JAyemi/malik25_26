module clk_phase_shifter (
  input clk,
  input [7:0] shift,
  output reg clk_shifted
);

parameter n = 8; // number of bits in the phase shift value

reg [n-1:0] shift_reg;
reg [n-1:0] shift_reg_next;
reg [n-1:0] shift_reg_last;
reg clk_shifted_last;
integer i;

always @(posedge clk) begin
  shift_reg_last <= shift_reg;
  clk_shifted_last <= clk_shifted;
end

always @(posedge clk) begin
  shift_reg_next[0] <= clk;
  for (i = 1; i < n; i = i + 1) begin
    shift_reg_next[i] <= shift_reg[i-1];
  end
end

always @(posedge clk) begin
  if (shift == 0) begin
    clk_shifted <= clk;
  end else begin
    clk_shifted <= shift_reg_last[n-1];
  end
end

always @(posedge clk) begin
  shift_reg <= shift_reg_next;
end

endmodule