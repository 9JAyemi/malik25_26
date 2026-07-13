
module clock_gate(
 input CLK,
 input EN,
 input TE,
 output ENCLK
);
reg ENCLK;
always @(EN or TE) begin
  if (EN)
    ENCLK = CLK;
  else if (TE)
    ENCLK = 1'b0;
  else
    ENCLK = 1'bx;
end
endmodule