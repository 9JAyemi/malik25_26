module oh_dsync  #(parameter PS    = 2,        parameter DELAY = 0         )
   (
    input  clk, input  nreset, input  din, output dout    );
   
`ifdef CFG_ASIC
   asic_dsync asic_dsync (.clk(clk),
			  .nreset(nreset),
			  .din(din),
			  .dout(dout));
`else
   reg [PS:0] sync_pipe; 
   always @ (posedge clk or negedge nreset)		 
     if(!nreset)
       sync_pipe[PS:0] <= 'b0;
     else
       sync_pipe[PS:0] <= {sync_pipe[PS-1:0],din};	      	      
   assign dout = (DELAY & sync_pipe[PS]) |  (~DELAY & sync_pipe[PS-1]); `endif endmodule 