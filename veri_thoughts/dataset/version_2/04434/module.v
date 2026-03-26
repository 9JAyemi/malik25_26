
module clock_gate (
  input CLK,
  input EN,
  input TE,
  output reg ENCLK
);

 always @(posedge TE or posedge CLK) begin
    if (TE == 0) ENCLK <= EN;
     else ENCLK <= 0;
 end

endmodule