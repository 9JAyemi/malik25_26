
module decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_mult_gen_v12_0_12
   (CLK,
    A,
    B,
    CE,
    SCLR,
    ZERO_DETECT,
    P,
    PCASC);
  input CLK;
  input [16:0]A;
  input [15:0]B;
  input CE;
  input SCLR;
  output [1:0]ZERO_DETECT;
  output [32:0]P;
  output [63:0]PCASC;
  wire GND;

  assign P = A * B;
  assign ZERO_DETECT = ((P == 0) ? 2'b11 : 2'b00);
  assign PCASC = 64'h0;
  assign GND = 0;
endmodule