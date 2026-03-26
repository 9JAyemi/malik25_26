
module DFF (
  input D, CLK,
  output Q
);

  reg Q;  // Change wire to reg

  always @(posedge CLK) begin
    Q <= D;
  end

endmodule

module SNPS_CLOCK_GATE_HIGH_FSM_Mult_Function (
  input CLK, EN, TE, CLK2, SEL,
  output ENCLK
);

  DFF latch ( .D(EN), .CLK(CLK) );

  wire gated_clk1;
  wire gated_clk2;

  assign gated_clk1 = CLK & EN;
  assign gated_clk2 = CLK2 & EN;

  assign ENCLK = SEL ? gated_clk2 : gated_clk1;

endmodule
