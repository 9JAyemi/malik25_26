module emesh_if (
   cmesh_ready_out, cmesh_access_out, cmesh_packet_out,
   rmesh_ready_out, rmesh_access_out, rmesh_packet_out,
   xmesh_ready_out, xmesh_access_out, xmesh_packet_out,
   emesh_ready_out, emesh_access_out, emesh_packet_out,
   cmesh_access_in, cmesh_packet_in, cmesh_ready_in, rmesh_access_in,
   rmesh_packet_in, rmesh_ready_in, xmesh_access_in, xmesh_packet_in,
   xmesh_ready_in, emesh_access_in, emesh_packet_in, emesh_ready_in
   );

   parameter AW   = 32;   
   parameter PW   = 2*AW+40; 

   input 	   cmesh_access_in;
   input [PW-1:0]  cmesh_packet_in;
   output 	   cmesh_ready_out;
   output 	   cmesh_access_out;
   output [PW-1:0] cmesh_packet_out;
   input 	   cmesh_ready_in;
      
   input 	   rmesh_access_in;
   input [PW-1:0]  rmesh_packet_in;
   output 	   rmesh_ready_out;
   output 	   rmesh_access_out;
   output [PW-1:0] rmesh_packet_out;
   input 	   rmesh_ready_in;
   
   input 	   xmesh_access_in;
   input [PW-1:0]  xmesh_packet_in;
   output 	   xmesh_ready_out;  
   output 	   xmesh_access_out;
   output [PW-1:0] xmesh_packet_out;
   input 	   xmesh_ready_in;
   
   input 	   emesh_access_in;
   input [PW-1:0]  emesh_packet_in;
   output 	   emesh_ready_out;
   
   output 	   emesh_access_out;
   output [PW-1:0] emesh_packet_out;
   input 	   emesh_ready_in;
      
   assign cmesh_access_out = emesh_access_in & emesh_packet_in[0];

   assign rmesh_access_out = emesh_access_in & ~emesh_packet_in[0];

   assign xmesh_access_out = 1'b0;
      
   assign cmesh_packet_out[PW-1:0] = emesh_packet_in[PW-1:0];	 
   assign rmesh_packet_out[PW-1:0] = emesh_packet_in[PW-1:0];	 
   assign xmesh_packet_out[PW-1:0] = emesh_packet_in[PW-1:0];


   assign emesh_ready_out = cmesh_ready_in &
			    rmesh_ready_in &
			    xmesh_ready_in;
  	 	 
   assign emesh_access_out = cmesh_access_in &
			     rmesh_access_in &
			     xmesh_access_in;
   

   assign emesh_packet_out[PW-1:0] = cmesh_access_in ? cmesh_packet_in[PW-1:0] :
				     rmesh_access_in ? rmesh_packet_in[PW-1:0] :
				                       xmesh_packet_in[PW-1:0];
   
   assign cmesh_ready_out = ~(cmesh_access_in & ~emesh_ready_in);
   

   assign rmesh_ready_out = ~(rmesh_access_in & 
			    (~emesh_ready_in | ~cmesh_ready_in));

   assign xmesh_ready_out = ~(xmesh_access_in & 
			      (~emesh_ready_in | ~cmesh_access_in | ~rmesh_access_in));
   
				     
endmodule 