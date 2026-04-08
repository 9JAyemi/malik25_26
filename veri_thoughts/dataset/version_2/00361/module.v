
module DFFE(CLK, D, EN, Q);
  input CLK, D, EN;
  output Q;

  reg Q;

  always @(posedge CLK) begin
    if (EN) begin
      Q <= D;
    end
  end

endmodule

module d_ff_en_gate(CLK, D, EN, TE, Q, ENCLK);
  input CLK, D, EN, TE;
  output Q, ENCLK;

  reg Q;
  wire gated_clk;

  DFFE gated_clk_inst(.CLK(CLK), .D(EN), .EN(TE), .Q(gated_clk));

  always @(posedge gated_clk) begin
    if (EN) begin
      Q <= D;
    end
  end

  assign ENCLK = gated_clk;

endmodule
