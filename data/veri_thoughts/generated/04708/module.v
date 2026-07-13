
module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W64_0_6 (
  input CLK, EN, TE, 
  output ENCLK, 
  output TLATNTSCAX2TS_E, 
  output TLATNTSCAX2TS_SE, 
  output TLATNTSCAX2TS_CK, 
  output TLATNTSCAX2TS_ECK
);

  reg ENCLK;

  always @(posedge CLK) begin
    if (EN) begin
      ENCLK <= 1'b1;
    end else begin
      ENCLK <= 1'b0;
    end
  end

  assign TLATNTSCAX2TS_E = EN;
  assign TLATNTSCAX2TS_SE = TE;
  assign TLATNTSCAX2TS_CK = CLK;
  assign TLATNTSCAX2TS_ECK = ENCLK;

endmodule