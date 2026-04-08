
module DFF (CLK, D, Q);
  input CLK, D;
  output Q;

  reg Q;

  always @(posedge CLK) begin
    Q <= D;
  end
endmodule
module SNPS_CLOCK_GATE_HIGH_Up_counter_COUNTER_WIDTH4 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  wire ENCLK_blocking_assign;
  DFF latch ( .CLK(CLK), .D(EN), .Q(ENCLK_blocking_assign) );

  assign ENCLK = TE ? ENCLK_blocking_assign : 1'b0;

endmodule