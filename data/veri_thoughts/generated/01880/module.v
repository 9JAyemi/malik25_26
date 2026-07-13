
module d_ff_en_clk_gate (
  input CLK,
  input EN,
  input TE,
  input [31:0] DATA_IN,
  output reg DATA_OUT
);

  reg d_ff_en;
  wire ENCLK;

endmodule

module TLATNTSCAX2TS (
    input E,
    input SE,
    input CK,
    output ECK
);

    assign ECK = E & SE & CK;

endmodule
