module mux4bit (MO, A, B, S);
   input [3:0] A, B;
   input       S;
   output [3:0] MO; 
   
   assign MO = (S == 1) ? B : A; 
   
endmodule