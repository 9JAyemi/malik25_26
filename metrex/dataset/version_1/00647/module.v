
module RIPPLEADD_64 (A, B, Cin, S, Cout);
input [63:0] A, B;
input Cin;
output [63:0] S;
output Cout;

wire [63:0] C;
assign C[0] = Cin;
genvar i;
generate
    for (i = 0; i < 63; i = i + 1) begin : full_adder
        FULLADDER_1BIT FA(
            .A(A[i]),
            .B(B[i]),
            .Cin(C[i]),
            .S(S[i]),
            .Cout(C[i+1])
        );
    end
endgenerate

assign Cout = C[63];
assign S[63] = C[63]; // Fixing the issue of undriven wire

endmodule
module FULLADDER_1BIT (A, B, Cin, S, Cout);
input A, B, Cin;
output S, Cout;

assign S = A ^ B ^ Cin;
assign Cout = (A & B) | (Cin & (A ^ B));

endmodule