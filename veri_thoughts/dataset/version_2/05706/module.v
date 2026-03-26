module cycloneive_b5mux21_extended (MO, A, B, S);
   input [31:0] A, B;
   input        S;
   output [31:0] MO; 
   
   assign MO = (S == 1) ? B : A; 
   
endmodule