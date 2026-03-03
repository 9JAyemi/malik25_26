module mux4to1(I, S, O);
  input [1:0] I;
  input [1:0] S;
  output O;

  assign O = (S == 2'b00) ? I[0] :
             (S == 2'b01) ? I[1] :
             (S == 2'b10) ? 1'b0 :
             (S == 2'b11) ? 1'b1 :
                            1'bx;
endmodule