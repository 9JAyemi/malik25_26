
module full_adder (
    input  wire [7:0] A,
    input  wire [7:0] B,
    output wire [8:0] S
);

    wire [8:0] C;

    // First adder
    assign {C[1], S[0]} = A[0] + B[0];

    // Middle adders
    genvar i;
    generate
        for (i = 1; i <= 6; i = i + 1) begin : adder_loop
            assign {C[i+1], S[i]} = A[i] + B[i] + C[i];
        end
    endgenerate

    // Last adder
    assign {C[8], S[7]} = A[7] + B[7] + C[7];
    assign S[8] = C[8];

endmodule