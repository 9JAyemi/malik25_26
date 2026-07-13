module XOR_M ( Sgn_X, Sgn_Y, Sgn_Info );
  input Sgn_X, Sgn_Y;
  output Sgn_Info;

  assign Sgn_Info = Sgn_X ^ Sgn_Y;

endmodule