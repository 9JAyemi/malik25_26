
module adder4 #(parameter WIDTH = 4)(
    input [WIDTH-1:0] A,
    input [WIDTH-1:0] B,
    input Cin,
    output [WIDTH-1:0] S,
    output Cout
);

    wire [WIDTH:0] C;

    assign C[0] = Cin;

    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : adder
            full_adder FA(
                .A(A[i]),
                .B(B[i]),
                .Cin(C[i]),
                .S(S[i]),
                .Cout(C[i+1])
            );
        end
    endgenerate

    assign Cout = C[WIDTH];

endmodule
module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    wire w1, w2, w3;

    assign w1 = A ^ B;
    assign w2 = A & B;
    assign w3 = w1 & Cin;
    assign S = w1 ^ Cin;
    assign Cout = w2 | w3;

endmodule