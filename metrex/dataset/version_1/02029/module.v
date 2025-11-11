
module comparator_4bit (
  input [3:0] A,
  input [3:0] B,
  input [3:0] C,
  input [3:0] D,
  output reg eq,
  output reg gt,
  output reg lt
);

  always @(*) begin
    eq = (A==B) && (B==C) && (C==D);
    gt = (A>B) && (B>C) && (C>D);
    lt = (A<B) && (B<C) && (C<D);
  end

endmodule
