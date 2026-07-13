
module FA_17 ( A, B, Ci, S, Co );
  input A, B, Ci;
  output S, Co;
  wire   n1, n2, n3, n4;

  xor ( n1, A, B );
  xor ( S, n1, Ci );
  and ( n2, A, B );
  and ( n3, n1, Ci );
  or  ( Co, n2, n3 );
endmodule
