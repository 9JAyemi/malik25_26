
module clk_divider( sysclk, slowclk );
   input 	sysclk; 	output 	slowclk;	reg [6:0] 	counter; reg		slowclock;

   initial begin
      counter = 0;
      slowclock = 1;
   end
   
   always @ (posedge sysclk) begin
		if(counter == 'D50) begin
			counter <= 0;
			slowclock <= ~slowclock;
		end else begin
			counter <= counter + 1;
		end
   end

   assign slowclk = slowclock;

endmodule
