
module logic_function ( A, B, Ci, S, Co );
  input A, B, Ci;
  output S, Co;
  wire   n1, n2, n3, n4, n5, n6, n7, n8, n9, n10;

  xor ( n1, A, B );
  xor ( S, n1, Ci );
  and ( n2, A, B );
  and ( n3, n2, Ci );
  not ( n4, A );
  not ( n5, B );
  and ( n6, n4, n5 );
  and ( n7, n6, Ci );
  and ( n8, n4, B );
  and ( n9, A, n5 );
  and ( n10, n8, n9 );
  or ( Co, n3, n7, n10 );
endmodule