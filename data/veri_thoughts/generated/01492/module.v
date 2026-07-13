module top_module (
    input A,
    input B,
    input C_in,
    output [8:0] out
);

    wire [1:0] fa1_out;
    wire [1:0] fa2_out;
    wire parity_bit;

    // Full Adder 1
    full_adder fa1 (
        .A(A),
        .B(B),
        .C_in(C_in),
        .sum(fa1_out[0]),
        .C_out(fa1_out[1])
    );

    // Full Adder 2
    full_adder fa2 (
        .A(fa1_out[0]),
        .B(fa1_out[1]),
        .C_in(1'b0),
        .sum(fa2_out[0]),
        .C_out(fa2_out[1])
    );

    // Parity Bit Calculation
    assign parity_bit = (A ^ B ^ fa2_out[0]) & (A | B | fa2_out[0]);

    // Output
    assign out = {parity_bit, fa2_out};

endmodule

// Full Adder
module full_adder (
    input A,
    input B,
    input C_in,
    output sum,
    output C_out
);

    assign sum = A ^ B ^ C_in;
    assign C_out = (A & B) | (C_in & (A ^ B));

endmodule