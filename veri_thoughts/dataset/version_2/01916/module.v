
module clock_gate (input CLK, EN, TE, output ENCLK);
  wire EN_gate, TE_gate, CLK_gate, ENCLK;
  
  TLATNTSCAX2TS latch (.E(EN_gate), .SE(TE_gate), .CK(CLK_gate), .ECK(ENCLK));
  assign CLK_gate = CLK;
  assign EN_gate = EN;
  assign TE_gate = TE;
endmodule
module TLATNTSCAX2TS (
  input E, SE, CK,
  output reg ECK
);

  always @(posedge CK) begin
    if (E)
      ECK <= SE;
  end

endmodule