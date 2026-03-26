module oh_oddr #(parameter DW  = 1) (
    input 	    clk, input [DW-1:0]  din1, input [DW-1:0]  din2, output [DW-1:0] out   );
   
   reg [DW-1:0]    q1_sl;   
   reg [DW-1:0]    q2_sl;
   reg [DW-1:0]    q2_sh;
      
   always @ (posedge clk)
     begin
	q1_sl[DW-1:0] <= din1[DW-1:0];
	q2_sl[DW-1:0] <= din2[DW-1:0];
     end
   
   always @ (negedge clk)
     q2_sh[DW-1:0] <= q2_sl[DW-1:0];
       
   assign out[DW-1:0] = clk ? q1_sl[DW-1:0] : 
	                      q2_sh[DW-1:0];
      
endmodule 