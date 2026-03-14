
module my_full_adder(
  input A,
  input B,
  input CI,
  output reg SUM,
  output reg COUT
);

always @(*) begin
  SUM = A ^ B ^ CI;
  COUT = (A & B) | (A & CI) | (B & CI);
end

endmodule
