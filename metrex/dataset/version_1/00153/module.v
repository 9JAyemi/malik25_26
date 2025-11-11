
module glitch_filter (
  input in,
  input clk, // clock signal
  output out
);

parameter n = 4; // number of clock cycles to filter out glitches

reg [n-1:0] shift_reg; // shift register with n stages
reg temp_out;

always @(posedge clk) begin
  // shift the values in the shift register
  shift_reg <= {shift_reg[n-2:0], in};
  
  // compare the values in the shift register
  if (shift_reg[0] != shift_reg[n-1] || shift_reg[0] != shift_reg[n-2] || shift_reg[0] != shift_reg[n-3]) begin
    // ignore the glitch
    temp_out <= 0;
  end else begin
    // output the filtered signal
    temp_out <= shift_reg[n-1];
  end
end

assign out = temp_out; 

endmodule