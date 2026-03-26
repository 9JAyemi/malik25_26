module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output [3:0] S,
    output COUT
);

    wire [3:0] sum;
    wire carry_out_1;
    wire carry_out_2;
    
    // First stage of the adder
    full_adder fa1(.A(A[0]), .B(B[0]), .CIN(CIN), .S(sum[0]), .COUT(carry_out_1));
    full_adder fa2(.A(A[1]), .B(B[1]), .CIN(carry_out_1), .S(sum[1]), .COUT(carry_out_2));
    full_adder fa3(.A(A[2]), .B(B[2]), .CIN(carry_out_2), .S(sum[2]), .COUT(COUT));
    full_adder fa4(.A(A[3]), .B(B[3]), .CIN(COUT), .S(sum[3]), .COUT());
    
    assign S = sum;
    
endmodule

module full_adder (
    input A,
    input B,
    input CIN,
    output S,
    output COUT
);

    assign S = A ^ B ^ CIN;
    assign COUT = (A & B) | (A & CIN) | (B & CIN);
    
endmodule