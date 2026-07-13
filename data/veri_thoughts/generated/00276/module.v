
module booth_encoder_7_new ( B_in, A_out );
  input [2:0] B_in;
  output [2:0] A_out;
  wire   n1, n2, n3, n4, n5, n6, n7;
  
  not (n1, B_in[0]);
  not (n2, B_in[1]);
  not (n3, B_in[2]);
  and (n4, n1, n2);
  and (n5, B_in[0], n2);
  and (n6, n1, B_in[1]);
  or (A_out[0], n5, n6);
  or (A_out[1], n4, n3);
  or (A_out[2], B_in[2], n6);
endmodule