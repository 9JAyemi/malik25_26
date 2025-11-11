
module update_TAGRAM (
   input clk_in,
   input srst,
   input [7:0] tx_length_dw,
   input [7:0] tx_tag,
   input tx_ack0,
   input [7:0] tx_fmt_type,
   input [7:0] rx_length_dw_byte,
   input [7:0] rx_tag,
   input rx_ack_reg,
   input [7:0] rx_fmt_type,
   output reg [7:0] tagram_data_a,
   output reg [7:0] tagram_address_a,
   output reg tagram_wren_a,
   output reg [7:0] tagram_data_b,
   output reg tagram_wren_b,
   output reg [7:0] tagram_address_b,
   output reg [4:0] read_tagram
);

   // TAGRAM port A
   always @ (posedge clk_in) begin
      tagram_address_a <= tx_tag;
      tagram_data_a <= tx_length_dw;
      tagram_wren_a <= ((tx_ack0==1'b1) &&
                           (tx_fmt_type[4:0]==5'b00000) &&
                           (tx_fmt_type[6]==1'b0)) ? 1'b1 : 1'b0;
   end

   // TAGRAM port B
   always @ (posedge clk_in) begin
      if (srst == 1'b1)
         tagram_address_b <= 8'b0;
      else if (rx_ack_reg == 1'b1) begin
         tagram_address_b <= rx_tag;
         tagram_data_b <= rx_length_dw_byte;
         tagram_wren_b <= 1'b1;
      end
      else
         tagram_wren_b <= 1'b0;
   end

   always @ (posedge clk_in) begin
      if (srst == 1'b1)
         read_tagram[0] <= 1'b0;
      else if ((rx_length_dw_byte >= 8'h0) &&
                 (rx_fmt_type[6:1] == 6'b100101) && (rx_ack_reg == 1'b1))
         read_tagram[0] <= 1'b1;
      else
         read_tagram[0] <= 1'b0;
   end

   always @ (posedge clk_in) begin
      read_tagram[1] <= read_tagram[0];
      read_tagram[2] <= read_tagram[1];
      read_tagram[3] <= read_tagram[2];
      read_tagram[4] <= read_tagram[3];
   end

endmodule