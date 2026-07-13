module adder4(A, B, Cin, S, Cout);

input [3:0] A;
input [3:0] B;
input Cin;
output [3:0] S;
output Cout;

wire [3:0] carry;
wire [3:0] sum;


// First full adder (least significant bit)
full_adder fa0(A[0], B[0], Cin, sum[0], carry[0]);

// Second full adder
full_adder fa1(A[1], B[1], carry[0], sum[1], carry[1]);

// Third full adder
full_adder fa2(A[2], B[2], carry[1], sum[2], carry[2]);

// Fourth full adder (most significant bit)
full_adder fa3(A[3], B[3], carry[2], sum[3], Cout);

// Output the sum
assign S = sum;

endmodule

// Full adder module
module full_adder(a, b, cin, s, cout);

input a;
input b;
input cin;
output s;
output cout;

// Implement the full adder logic
assign s = a ^ b ^ cin;
assign cout = (a & b) | (cin & (a ^ b));

endmodule