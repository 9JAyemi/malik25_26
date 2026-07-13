module axi_timer
   #(parameter INIT_VALUE = 16'h1000)
   (input [4:0] bus2ip_addr_i_reg,
    input Q,
    output reg ce_expnd_i_5);

  wire [3:0] lut_input;
  assign lut_input = {bus2ip_addr_i_reg[2], Q, bus2ip_addr_i_reg[1:0]};

  always @*
    case (lut_input)
      4'b0000: ce_expnd_i_5 = 1'b0;
      4'b0001: ce_expnd_i_5 = 1'b0;
      4'b0010: ce_expnd_i_5 = 1'b0;
      4'b0011: ce_expnd_i_5 = 1'b0;
      4'b0100: ce_expnd_i_5 = 1'b0;
      4'b0101: ce_expnd_i_5 = 1'b0;
      4'b0110: ce_expnd_i_5 = 1'b0;
      4'b0111: ce_expnd_i_5 = 1'b0;
      4'b1000: ce_expnd_i_5 = 1'b1;
      4'b1001: ce_expnd_i_5 = 1'b0;
      4'b1010: ce_expnd_i_5 = 1'b0;
      4'b1011: ce_expnd_i_5 = 1'b0;
      4'b1100: ce_expnd_i_5 = 1'b0;
      4'b1101: ce_expnd_i_5 = 1'b0;
      4'b1110: ce_expnd_i_5 = 1'b0;
      4'b1111: ce_expnd_i_5 = 1'b0;
    endcase

endmodule