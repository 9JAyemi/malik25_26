module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W31_0_2 (input CLK, EN, TE, output ENCLK);

  wire D;
  // TLATNTSCAX2TS latch (.E(EN), .SE(TE), .CK(CLK), .Q(D));
  TLATNTSCAX2TS latch (EN, TE, CLK, D);
  assign ENCLK = D;
  
endmodule 

module TLATNTSCAX2TS (E, SE, CK, Q);
  input E, SE, CK;
  output Q;
  
  reg Q;

  always @(posedge CK) begin
    if (E)
      Q <= SE;
  end
endmodule