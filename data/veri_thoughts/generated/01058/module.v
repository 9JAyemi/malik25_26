module strobe_gen 
  ( input clock,
    input reset,
    input enable,
    input [7:0] rate, input strobe_in,
    output wire strobe );
   
reg [7:0] counter;
   assign strobe = ~|counter && enable && strobe_in;
   
   always @(posedge clock)
     if(reset | ~enable)
       counter <= #1 8'd0;
     else if(strobe_in)
       if(counter == 0)
	 counter <= #1 rate;
       else 
	 counter <= #1 counter - 8'd1;
   
endmodule 