
module my_module (
  Ar,
  Aa,
  Br,
  Ba
);

  input Ar;
  output Aa;
  output Br;
  input Ba;

  wire s_0n;

  assign Aa = Ar & Ba;
  assign s_0n = Aa;
  assign Br = !s_0n;

endmodule
