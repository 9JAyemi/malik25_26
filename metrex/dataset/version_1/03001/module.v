

module spi_core (
   o_sdo, o_drvb, o_spi_active, o_rx_valid, vo_byte_num, vo_data_rx,
   i_rstb, i_cs, i_sck, i_sdi, i_epol, i_cpol, i_cpha, vi_data_tx
   );
   parameter BITS_IN_BYTE = 8;
   parameter NBIT_BIT_CTR = 3;
   parameter NBIT_BYTE_CTR = 3;
   
   input 		      i_rstb;
   input 		      i_cs; input 		      i_sck; input 		      i_sdi; output 		      o_sdo; output 		      o_drvb; input 		      i_epol; input 		      i_cpol; input 		      i_cpha;
   output 		      o_spi_active; output 		      o_rx_valid; output [NBIT_BYTE_CTR-1:0] vo_byte_num; input [BITS_IN_BYTE-1:0]   vi_data_tx; output [BITS_IN_BYTE-1:0]  vo_data_rx; reg 			      o_rx_valid;
   reg [NBIT_BYTE_CTR-1:0]    vo_byte_num;

   
   wire 		      chip_select; 
   wire 		      sck_core; 
   assign chip_select = i_rstb && (i_epol ^ i_cs);
   assign o_spi_active = chip_select;
   assign sck_core = i_cpha ^ i_cpol ^ i_sck;
   assign o_drvb = !chip_select;
   
   reg [BITS_IN_BYTE-1:0]     rv_tx;
   reg [NBIT_BIT_CTR-1:0]     rv_tx_ptr;
   always @( negedge sck_core or negedge chip_select ) begin : tx_fsm
      if ( !chip_select ) begin
	 rv_tx_ptr <= $unsigned(BITS_IN_BYTE - 1);
	 vo_byte_num <= 0;
	 rv_tx <= 0;
      end else begin
	 if ( 0 == rv_tx_ptr ) begin
	    rv_tx <= vi_data_tx;
	    rv_tx_ptr <= $unsigned(BITS_IN_BYTE - 1);
	    vo_byte_num <= vo_byte_num + 1;
	 end else begin
	    rv_tx_ptr <= rv_tx_ptr - 1;
	 end
      end end assign o_sdo = rv_tx[rv_tx_ptr];
   
   reg [BITS_IN_BYTE-2:0]     rv_rx;
   always @( posedge sck_core or negedge chip_select ) begin : rx_fsm
      if ( !chip_select ) begin
	 rv_rx <= 0;
         o_rx_valid <= 0;
      end else begin
	 if ( 0 == rv_tx_ptr ) begin
	    o_rx_valid <= 1;   
	 end else begin
	    o_rx_valid <= 0;
            rv_rx[BITS_IN_BYTE-2:1] <= rv_rx[BITS_IN_BYTE-3:0];
	    rv_rx[0] <= i_sdi;
	 end end end assign vo_data_rx = {rv_rx,i_sdi};
endmodule
