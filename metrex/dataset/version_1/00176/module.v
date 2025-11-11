
module four_bit_subtractor(
 input [3:0] A,
 input [3:0] B,
 output [3:0] C,
 output Borrow
);

  wire [3:0] diff;
  wire borrow1, borrow2;

 one_bit_subtractor obs1(
 .A(A[0]),
 .B(B[0]),
 .Bin(1'b0),
 .Diff(diff[0]),
 .BorrowOut(borrow1)
 );

 one_bit_subtractor obs2(
 .A(A[1]),
 .B(B[1]),
 .Bin(borrow1),
 .Diff(diff[1]),
 .BorrowOut(borrow2)
 );

 one_bit_subtractor obs3(
 .A(A[2]),
 .B(B[2]),
 .Bin(borrow2),
 .Diff(diff[2]),
 .BorrowOut(Borrow)
 );

  assign diff[3] = A[3] ^ B[3] ^ Borrow;
  assign C = diff;

endmodule
module one_bit_subtractor(
 input A,
 input B,
 input Bin,
 output Diff, 
 output BorrowOut
 );

  assign Diff = A ^ B ^ Bin;
  assign BorrowOut = (~A & B) | (~A & Bin) | (B & Bin);

endmodule