
module SR_FF_D_FFSR_MUX (
  input D, S, R, CLK,
  output Q
);

  wire D_FF_Q;
  wire MUX_OUT;

  // Instantiate the D-FFSR
  D_FF_SR d_ff_sr (
    .D(D),
    .S(S),
    .R(R),
    .CLK(CLK),
    .Q(D_FF_Q)
  );

  // Instantiate the MUX
  MUX2x1 mux (
    .IN0(D_FF_Q),
    .IN1(R),  // Corrected the input to match the MUX behavior
    .SEL(S),
    .OUT(MUX_OUT)
  );

  assign Q = ~MUX_OUT; // Fix the RTL

endmodule
module D_FF_SR (
  input D, S, R, CLK,
  output Q
);

  reg Q_reg;

  always @(posedge CLK) begin
    if (R) Q_reg <= 1'b0;
    else if (S) Q_reg <= 1'b1;
    else Q_reg <= D;
  end

  assign Q = Q_reg;

endmodule
module MUX2x1 (
  input IN0, IN1, SEL,
  output OUT
);

  assign OUT = SEL ? IN1 : IN0;

endmodule