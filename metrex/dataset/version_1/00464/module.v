
module mux4to1(D0, D1, D2, D3, S0, S1, Y);
   input D0, D1, D2, D3, S0, S1;
   output Y;
   
   wire notS0, notS1, notS0andS1, S0andnotS1, notS0andnotS1, S0andS1;
   
   //inverting select signals
   assign notS0 = ~S0;
   assign notS1 = ~S1;
   
   //creating intermediate signals for output
   assign notS0andS1 = notS0 & S1;
   assign S0andnotS1 = S0 & notS1;
   assign notS0andnotS1 = notS0 & notS1;
   assign S0andS1 = S0 & S1;
   
   //multiplexer output
   assign Y = (D0 & notS0andnotS1) |
               (D1 & S0andnotS1) |
               (D2 & notS0andS1) |
               (D3 & S0andS1);
endmodule
