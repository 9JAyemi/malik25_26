module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    wire [3:0] xor_out;
    wire [3:0] and_out;
    
    // XOR gates for the sum
    assign xor_out[0] = A[0] ^ B[0];
    assign xor_out[1] = A[1] ^ B[1];
    assign xor_out[2] = A[2] ^ B[2];
    assign xor_out[3] = A[3] ^ B[3];
    
    // AND gates for the carry
    assign and_out[0] = A[0] & B[0];
    assign and_out[1] = A[1] & B[1];
    assign and_out[2] = A[2] & B[2];
    assign and_out[3] = A[3] & B[3];
    
    // Generate carry out
    assign Cout = (and_out[0] & and_out[1]) | (and_out[1] & and_out[2]) | (and_out[2] & and_out[3]) | (and_out[3] & Cin);
    
    // Generate sum
    assign Sum[0] = xor_out[0] ^ Cin;
    assign Sum[1] = xor_out[1] ^ and_out[0];
    assign Sum[2] = xor_out[2] ^ and_out[1];
    assign Sum[3] = xor_out[3] ^ and_out[2];

endmodule