
module ripple_carry_adder(A, B, CIN, SUM, COUT);
input [3:0] A, B;
input CIN;
output [3:0] SUM;
output COUT;

wire [3:0] CARRY;

FA FA0(A[0], B[0], CIN, SUM[0], CARRY[0]);
FA FA1(A[1], B[1], CARRY[0], SUM[1], CARRY[1]);
FA FA2(A[2], B[2], CARRY[1], SUM[2], CARRY[2]);
FA FA3(A[3], B[3], CARRY[2], SUM[3], COUT);

endmodule
module FA(A, B, CIN, SUM, COUT);
input A, B, CIN;
output SUM, COUT;

wire XOR1, XOR2;

assign XOR1 = A ^ B;
assign XOR2 = XOR1 ^ CIN;
assign SUM = XOR2;
assign COUT = (A & B) | (A & CIN) | (B & CIN);

endmodule