module mux_2_to_1_en(
  input a,
  input b,
  input en,
  output out
);

  assign out = en ? b : a;

endmodule