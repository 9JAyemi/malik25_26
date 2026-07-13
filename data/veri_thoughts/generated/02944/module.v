
module SNPS_CLOCK_GATE_HIGH_ShiftRegister_W7_54 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  reg [6:0] shift_reg;
  wire [6:0] shifted_reg;
  wire latch_ECK;

  TLATNTSCAX2TS latch ( .E(EN & ENCLK), .SE(shift_reg[6]), .CK(CLK), .ECK(latch_ECK) );

  always @(posedge CLK) begin
    if (EN & ENCLK) begin
      shift_reg <= {shift_reg[5:0], TE};
    end
  end

  assign shifted_reg = {shift_reg[5:0], shift_reg[6]};
  assign ENCLK = latch_ECK;
endmodule
module TLATNTSCAX2TS (E, SE, CK, ECK);
  input E, SE, CK;
  output ECK;

  reg Q;

  always @(posedge CK) begin
    if (E) begin
      Q <= SE;
    end
  end

  assign ECK = Q;
endmodule