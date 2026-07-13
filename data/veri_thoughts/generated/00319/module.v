module three_bit_adder (input A, input B, input Ci, output S, output Co);

wire n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11;

assign n1 = A ^ B;
assign S = n1 ^ Ci;
assign n2 = A & B;
assign n3 = n1 & Ci;
assign Co = n2 | n3;
assign n4 = n2 & n3;
assign n5 = n4 | n3;
assign n6 = ~n5;
assign n7 = n2 & n3;
assign n8 = n1 & Ci;
assign n9 = n7 | n8;
assign n10 = ~n9;
assign n11 = n2 & n3;

endmodule