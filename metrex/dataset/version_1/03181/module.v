
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output [3:0] SUM,
    output COUT
);

    wire [3:0] carry;
    assign carry[0] = CIN;
    
    genvar i;
    generate
        for (i = 0; i < 3; i = i + 1) begin : adder
            full_adder fa(
                .A(A[i]),
                .B(B[i]),
                .CIN(carry[i]),
                .SUM(SUM[i]),
                .COUT(carry[i+1])
            );
        end
    endgenerate
    
    assign SUM[3] = A[3] ^ B[3] ^ carry[3];
    assign COUT = carry[3];

endmodule

module full_adder (
    input A,
    input B,
    input CIN,
    output SUM,
    output COUT
);

    assign SUM = A ^ B ^ CIN;
    assign COUT = (A & B) | (A & CIN) | (B & CIN);

endmodule
