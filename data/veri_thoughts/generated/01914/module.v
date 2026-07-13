module my_module (
  input in0, in1, in2, in3, d0, d1, d2, d3, clk, reset,
  output reg out0, out1, out2, out3
);

  wire n1, n2, n3, n4;

  assign n1 = ~(reset | n1);
  assign n2 = (in0 & d0) | (in1 & ~d0);
  assign n3 = ~(reset | n3);
  assign n4 = (in2 & d3) | (in3 & ~d3);

  always @(posedge clk) begin
    out0 <= d0;
    out1 <= d1;
    out2 <= d2;
    out3 <= d3;
  end

endmodule