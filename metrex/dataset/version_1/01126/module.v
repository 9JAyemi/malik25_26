
module emesh_if (
   // Outputs
   cmesh_ready_out, cmesh_access_out, cmesh_packet_out,
   rmesh_ready_out, rmesh_access_out, rmesh_packet_out,
   xmesh_ready_out, xmesh_access_out, xmesh_packet_out,
   emesh_ready_out, emesh_access_out, emesh_packet_out,
   // Inputs
   cmesh_access_in, cmesh_packet_in, cmesh_ready_in, rmesh_access_in,
   rmesh_packet_in, rmesh_ready_in, xmesh_access_in, xmesh_packet_in,
   xmesh_ready_in, emesh_access_in, emesh_packet_in, emesh_ready_in
   );

   parameter AW   = 32;   
   parameter PW   = 2*AW+40; 

   //##Cmesh##    
   input 	   cmesh_access_in;
   input [PW-1:0]  cmesh_packet_in;
   output 	   cmesh_ready_out;
   output 	   cmesh_access_out;
   output [PW-1:0] cmesh_packet_out;
   input 	   cmesh_ready_in;
      
   //##Rmesh## 
   input 	   rmesh_access_in;
   input [PW-1:0]  rmesh_packet_in;
   output 	   rmesh_ready_out;
   output 	   rmesh_access_out;
   output [PW-1:0] rmesh_packet_out;
   input 	   rmesh_ready_in;
   
   //##Xmesh## 
   input 	   xmesh_access_in;
   input [PW-1:0]  xmesh_packet_in;
   output 	   xmesh_ready_out;  
   output 	   xmesh_access_out;
   output [PW-1:0] xmesh_packet_out;
   input 	   xmesh_ready_in;
   
   //##Emesh##
   input 	   emesh_access_in;
   input [PW-1:0]  emesh_packet_in;
   output 	   emesh_ready_out;
   output 	   emesh_access_out;
   output [PW-1:0] emesh_packet_out;
   input 	   emesh_ready_in;
      
   //#####################################################
   //# EMESH-->(RMESH/XMESH/CMESH)
   //#####################################################
      
   assign cmesh_access_out = emesh_access_in & emesh_packet_in[0];

   assign rmesh_access_out = emesh_access_in & ~emesh_packet_in[0];

   //Don't drive on xmesh for now
   assign xmesh_access_out = 1'b0;
      
   //Distribute emesh to xmesh,cmesh, rmesh
   assign cmesh_packet_out = emesh_packet_in;	 
   assign rmesh_packet_out = emesh_packet_in;	 
   assign xmesh_packet_out = emesh_packet_in;

   assign emesh_ready_out = cmesh_ready_in &
			    rmesh_ready_in &
			    xmesh_ready_in;
  	 	 
   //#####################################################
   //# (RMESH/XMESH/CMESH)-->EMESH
   //#####################################################

   assign emesh_access_out = cmesh_access_in &
			     rmesh_access_in &
			     xmesh_access_in;
   
   //Choose the module to send packet to in a round-robin fashion
   reg [1:0] round_robin;
   always @(posedge emesh_ready_in) begin
      if (cmesh_access_in) round_robin <= 2'b01;
      else if (rmesh_access_in) round_robin <= 2'b10;
      else if (xmesh_access_in) round_robin <= 2'b00;
   end
   
   wire [PW-1:0] sel_packet;
   assign sel_packet = (round_robin == 2'b01) ? cmesh_packet_in :
                                     ((round_robin == 2'b10) ? rmesh_packet_in : xmesh_packet_in);
   
   assign cmesh_ready_out = ~(cmesh_access_in & ~emesh_ready_in);
   
   assign rmesh_ready_out = ~(rmesh_access_in & 
			    (~emesh_ready_in | ~cmesh_ready_in));

   assign xmesh_ready_out = ~(xmesh_access_in & 
			      (~emesh_ready_in | ~cmesh_access_in | ~rmesh_access_in));
   
   assign emesh_packet_out = sel_packet;
				     
endmodule
