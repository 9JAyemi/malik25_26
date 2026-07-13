module oh_iddr #(parameter DW      = 1 )
   (
    input 		clk, input 		ce, input [DW-1:0] 	din, output reg [DW-1:0] q1, output reg [DW-1:0] q2   );
   
   reg [DW-1:0]     q1_sl;
   reg [DW-1:0]     q2_sh;
   
   always @ (posedge clk)
     if(ce)
       q1_sl[DW-1:0] <= din[DW-1:0];
   
   always @ (negedge clk)
     q2_sh[DW-1:0] <= din[DW-1:0];
   
   always @ (posedge clk)
     begin
	q1[DW-1:0] <= q1_sl[DW-1:0];
	q2[DW-1:0] <= q2_sh[DW-1:0];
     end
            
endmodule 