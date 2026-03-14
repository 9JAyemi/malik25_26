
module latch (
  input E,
  input SE,
  input CK,
  output ECK
);

  reg gated_clk;

  always @(posedge CK) begin
    if (E && !SE) begin
      gated_clk <= 1'b1;
    end else begin
      gated_clk <= 1'b0;
    end
  end

  assign ECK = gated_clk;

endmodule

module clock_gate (
  input CLK,
  input EN,
  input TE,
  output ENCLK
);

  reg gated_clk;

  always @(posedge CLK) begin
    if (EN && !TE) begin
      gated_clk <= 1'b1;
    end else begin
      gated_clk <= 1'b0;
    end
  end

  latch latch (
    .E(EN),
    .SE(TE),
    .CK(CLK),
    .ECK(ENCLK)
  );

endmodule
