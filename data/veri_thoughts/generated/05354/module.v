
module clock_gate_d_ff_en (
  input CLK, EN, TE,
  output reg ENCLK
);

  reg gated_clk;

  always @ (posedge CLK)
  begin
    if (TE)
      gated_clk <= EN;
  end

  always @*
  begin
    if (EN == 1'b0)
      ENCLK <= 1'b0;
    else
      ENCLK <= gated_clk;
  end

endmodule