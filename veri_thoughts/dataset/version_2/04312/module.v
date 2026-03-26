module mux_4to1 (
  input in0,
  input in1,
  input in2,
  input in3,
  input sel1,
  input sel2,
  output out
);

  assign out = (sel1 & sel2) ? in3 : (sel1 & ~sel2) ? in2 : (~sel1 & sel2) ? in1 : in0;

endmodule