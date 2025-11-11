module pulses(
	      
	      input 	   clk_pll, input 	   clk, input [23:0]  per, input [15:0] p1wid,
	      input [15:0] del,
	      input [15:0] p2wid,
	      input 	   cp,
              input 	   bl,
	      input 	   rxd,
	      output 	   sync_on, output 	   pulse_on, output 	   inhib );

   reg [31:0] 		   counter = 0; reg 			   sync;
   reg 			   pulse;
   reg 			   inh;
   reg 			   rec = 0;
   reg 			   cw = 0; 			   
   
   parameter stperiod = 100500 >> 8; reg [23:0] 		   period = stperiod;
   reg [15:0] 		   p1width;
   reg [15:0] 		   delay;
   reg [15:0] 		   p2width;
   reg 			   cpmg;
   reg 			   block;
   reg [7:0] 		   pulse_block = 8'd50;
   reg 			   rx_done;
   reg [15:0] 		   p2start;
   reg [23:0] 		   sync_down;
   reg [15:0] 		   block_off;

   assign sync_on = sync; assign pulse_on = pulse; assign inhib = inh; always @(posedge clk) begin
      period <= per;
	 p1width <= p1wid;
	 p2width <= p2wid;
	 delay <= del;
	 cpmg <= cp;
	 block <= bl;

      p2start <= p1width + delay;
      sync_down <= (cpmg > 0) ? p2start + p2width : period << 7;
      block_off <= p2start + p2width + delay - pulse_block;

      cw <= (cpmg > 0) ? 0 : 1;
	 
   end

   
   always @(posedge clk_pll) begin
      case (counter)
	0: begin
	   pulse <= 1;
	   inh <= block;
	   sync <= 1;
	end

	p1width: begin
	   pulse <= cw;
	end

	p2start: begin
	   pulse <= 1;
	end

	sync_down: begin
	   pulse <= cw;
	   sync <= 0;
	end

	block_off: begin
	   inh <= 0;
	end
	
      endcase counter <= (counter < (period << 8)) ? counter + 1 : 0; end endmodule 