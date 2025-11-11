module majority_circuit (
  input a,
  input b,
  input c,
  output reg out
);

  always @ (a, b, c) begin
    out = (a & b) | (b & c) | (c & a);
  end
  
endmodule
