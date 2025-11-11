module user_design
   (IN1_STB,
    OUT1_ACK,
    output_rs232_out,
    INTERNAL_RST_reg,
    OUT1,
    IN1_ACK,
    ETH_CLK_OBUF,
    OUT1_STB);
  output IN1_STB;
  output OUT1_ACK;
  output [7:0]output_rs232_out;
  input INTERNAL_RST_reg;
  input [7:0]OUT1;
  input IN1_ACK;
  input ETH_CLK_OBUF;
  input OUT1_STB;

  assign IN1_STB = (INTERNAL_RST_reg == 1'b0) && (IN1_ACK == 1'b1) && (OUT1_STB == 1'b0);
  assign OUT1_ACK = (INTERNAL_RST_reg == 1'b0) && (OUT1_STB == 1'b1);
  assign output_rs232_out = (INTERNAL_RST_reg == 1'b0) && (OUT1_STB == 1'b1) ? OUT1 : 8'h0;

endmodule