
module IBUFCTRL (
  input I,
  input IBUFDISABLE,
  input T,
  output O
);

  assign O = IBUFDISABLE ? (T ? 1'b0 : 1'b1) : I;

endmodule