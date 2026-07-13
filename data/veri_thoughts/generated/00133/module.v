module binary_adder(
    input [3:0] A, 
    input [3:0] B, 
    input CIN, 
    output [3:0] S, 
    output COUT
);

    wire [3:0] sum;
    wire [3:0] carry;

    // Full Adder
    full_adder fa0(.A(A[0]), .B(B[0]), .CIN(CIN), .S(sum[0]), .COUT(carry[0]));
    full_adder fa1(.A(A[1]), .B(B[1]), .CIN(carry[0]), .S(sum[1]), .COUT(carry[1]));
    full_adder fa2(.A(A[2]), .B(B[2]), .CIN(carry[1]), .S(sum[2]), .COUT(carry[2]));
    full_adder fa3(.A(A[3]), .B(B[3]), .CIN(carry[2]), .S(sum[3]), .COUT(COUT));

    assign S = sum;

endmodule

module full_adder(
    input A, 
    input B, 
    input CIN, 
    output S, 
    output COUT
);

    assign S = A ^ B ^ CIN;
    assign COUT = (A & B) | (CIN & (A ^ B));

endmodule