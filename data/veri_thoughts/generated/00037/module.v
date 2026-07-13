
module latch (E, SE, CK, ECK);
  input E, SE, CK;
  output ECK;

  reg D;

  always @(posedge CK) begin
    if (E & SE) begin
      D <= 1;
    end else if (~E & SE) begin
      D <= 0;
    end
  end

  assign ECK = D;
endmodule

module clock_gate (CLK, EN, TE, ENCLK);
  input CLK, EN, TE;
  output ENCLK;

  reg D;
  wire G;

  assign G = EN & TE;
  always @(posedge CLK) begin
    if (G) begin
      D <= 1;
    end else begin
      D <= 0;
    end
  end

  latch latch_instance (.E(EN), .SE(TE), .CK(CLK), .ECK(ENCLK));

endmodule
