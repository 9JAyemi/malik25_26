
module ripple_carry_adder (
    input [15:0] A,
    input [15:0] B,
    input Cin,
    output [15:0] Sum
);

    wire [16:0] carry; // Adjusted the size to 17 bits
    assign carry[0] = Cin;

    genvar i;
    generate
        for (i = 0; i < 16; i = i + 1) begin : adder_stage
            full_adder adder(A[i], B[i], carry[i], Sum[i], carry[i+1]);
        end
    endgenerate

endmodule

module full_adder (
    input A,
    input B,
    input Cin,
    output Sum,
    output Cout
);

    assign Sum = A ^ B ^ Cin;
    assign Cout = (A & B) | (A & Cin) | (B & Cin);

endmodule
