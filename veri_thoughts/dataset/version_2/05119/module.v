
module oh_iddr #(parameter DW      = 1 // width of data inputs
		 )
   (
    input 		clk, // clock
    input 		ce0, // 1st cycle enable
    input 		ce1, // 2nd cycle enable
    input [DW/2-1:0] 	din, // data input sampled on both edges of clock
    output reg [DW-1:0] dout // iddr aligned
    );
   
   reg [DW/2-1:0]     din_sl;
   reg [DW/2-1:0]     din_sh;
   reg 		      ce0_negedge;
   
   //########################
   // Pipeline valid for negedge
   //########################
   always @(posedge clk)
     ce0_negedge <= ce0;

   //########################
   // Dual edge sampling
   //########################

   always @(posedge clk)
     if (ce0)
       din_sl <= din;
   always @(negedge clk)
     if (ce0_negedge)
       din_sh <= din;

   //########################
   // Aign pipeline
   //########################
   always @(posedge clk)
     if (ce1)
       dout <= {din_sh, din_sl};

endmodule