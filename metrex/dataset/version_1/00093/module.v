module clock_gate (CLK, EN, TE, ENCLK);
  input CLK, EN, TE;
  output ENCLK;

  reg gated_clk;

  always @ (posedge CLK) begin
    if (EN && !TE) begin
      gated_clk <= 1;
    end else begin
      gated_clk <= 0;
    end
  end

  assign ENCLK = gated_clk & CLK;

endmodule