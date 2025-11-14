
module dff(D, CLK, Q);
  input D, CLK;
  output Q;

  reg Q;

  always @(posedge CLK) begin
    Q <= D;
  end
endmodule
