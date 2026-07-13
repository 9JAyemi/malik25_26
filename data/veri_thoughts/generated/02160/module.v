
module gated_d_ff_en_W32_0_0 ( CLK, EN, TE, D, Q );
  input CLK, EN, TE;
  input [31:0] D;
  output [31:0] Q;

  wire gated_clk;

  TLATCH latch ( .E(EN), .SE(TE), .CK(CLK), .ECK(gated_clk) );

  reg [31:0] Q_reg;

  always @(posedge gated_clk) begin
    if (EN) begin
      Q_reg <= D;
    end
  end

  assign Q = Q_reg;


endmodule

module TLATCH ( E, SE, CK, ECK );
  parameter INIT = 1'b0;

  input  E, SE;
  input  CK;
  output ECK;

  reg ECK_int;

  assign ECK = ECK_int;

  initial ECK_int = INIT;

  always @( posedge CK ) begin
    if ( SE == 1'b1 ) ECK_int <=INIT;
    else if ( E == 1'b1 ) ECK_int <= 1'b1;
  end

endmodule
