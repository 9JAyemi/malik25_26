module xor_gate(
    input a,
    input b,
    output reg out
);

always @(a, b)
    out = (a & ~b) | (~a & b);

endmodule
