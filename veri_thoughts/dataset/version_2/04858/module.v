module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input C_in,
    output [3:0] S,
    output C_out
);

wire [3:0] sum;
wire [3:0] carry;

// Full adder for the least significant bit
full_adder FA0(A[0], B[0], C_in, sum[0], carry[0]);

// Carry propagation for the remaining bits
genvar i;
generate
    for(i = 1; i < 4; i = i + 1) begin : carry_gen
        full_adder FA(A[i], B[i], carry[i-1], sum[i], carry[i]);
    end
endgenerate

assign S = sum;
assign C_out = carry[3];

endmodule

module full_adder(
    input A,
    input B,
    input C_in,
    output S,
    output C_out
);

wire sum1;
wire C1;
wire C2;

// First XOR gate
xor(sum1, A, B);

// Second XOR gate
xor(S, sum1, C_in);

// First AND gate
and(C1, A, B);

// Second AND gate
and(C2, sum1, C_in);

// OR gate
or(C_out, C1, C2);

endmodule