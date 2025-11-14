
module verilog_module
  (input clk, input reset,
   input cyc_i, input stb_i, input we_i, output ack_o,
   input [31:0] dat_i, output [31:0] dat_o);

   wire 	BUSY, CE, WRITE;
   
   reg [2:0] 	icap_state;
   localparam ICAP_IDLE  = 3'b000;
   localparam ICAP_WR0 	 = 3'b001;
   localparam ICAP_WR1 	 = 3'b010;
   localparam ICAP_RD0 	 = 3'b011;
   localparam ICAP_RD1 	 = 3'b100;

   always @(posedge clk)
   if(reset)
     icap_state 	<= ICAP_IDLE;
   else
   begin
     case(icap_state)
	 ICAP_IDLE :
	   begin
	      if((cyc_i == 1 && stb_i == 1))
		if(we_i)
		  icap_state <= ICAP_WR0;
		else
		  icap_state <= ICAP_RD0;
	   end
	 ICAP_WR0 :
	   icap_state <= ICAP_WR1;
	 ICAP_WR1 :
	   icap_state <= ICAP_IDLE;
	 ICAP_RD0 :
	   icap_state <= ICAP_RD1;
	 ICAP_RD1 :
	   icap_state <= ICAP_IDLE;
     endcase // case (icap_state)
   end

   assign WRITE 	 = (icap_state == ICAP_WR0) | (icap_state == ICAP_WR1);
   assign CE 		 = (icap_state == ICAP_WR1) | (icap_state == ICAP_RD0);

   assign ack_o = (icap_state == ICAP_WR1) | (icap_state == ICAP_RD1);
   
   // RTL
   assign dat_o = (CE == 0) ? dat_i : ( (WRITE == 0) ? 32'b0 : 32'b1);

endmodule