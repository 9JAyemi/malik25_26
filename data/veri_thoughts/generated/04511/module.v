module mux2 (
	   input a,
	   input b,
	   output reg q);

   always @ (a, b) begin
     if (b == 1) begin
       q = a;
     end else begin
       q = b;
     end
   end
endmodule