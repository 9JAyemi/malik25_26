module logic_circuit (
  input a,
  input b,
  input c,
  input d,
  output out
);

  wire out;

  assign out = (a & b & c & d);

endmodule