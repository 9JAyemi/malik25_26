module XOR(A, B, C);
    input [7:0] A;
    input [7:0] B;
    output [7:0] C;

    genvar i;
    generate
        for (i = 0; i < 8; i = i + 1) begin
            assign C[i] = ~(A[i] & B[i]) & (A[i] | B[i]);
        end
    endgenerate
endmodule