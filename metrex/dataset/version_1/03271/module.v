module xor3 (
    input a,
    input b,
    input c,
    output x
);

    wire not_a;
    wire not_b;
    wire not_c;
    wire a_and_b;
    wire b_and_c;
    wire c_and_a;
    wire xor1;
    wire xor2;

    // Invert input bits
    not not_a (not_a, a);
    not not_b (not_b, b);
    not not_c (not_c, c);

    // Compute ANDs
    and a_and_b (a_and_b, a, b);
    and b_and_c (b_and_c, b, c);
    and c_and_a (c_and_a, c, a);

    // Compute XORs
    xor xor1 (xor1, not_a, b_and_c);
    xor xor2 (xor2, a_and_b, not_c);

    // Compute final XOR
    xor x (x, xor1, xor2);

endmodule