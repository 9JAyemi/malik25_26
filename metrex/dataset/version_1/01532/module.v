
module schmitt_trigger (
  input in,
  input clk,
  output out
);

parameter vth = 1'b1; // threshold voltage for switching from low to high
parameter vtl = 1'b0; // threshold voltage for switching from high to low
parameter hysteresis = 1'b1; // difference between vth and vtl

reg out_reg; // output register
reg prev_in; // previous input value

always @(posedge clk) begin
  if (in > (vth + hysteresis)) begin
    out_reg <= 1'b1;
  end else if (in < (vtl - hysteresis)) begin
    out_reg <= 1'b0;
  end
  prev_in <= in;
end

assign out = out_reg;

endmodule