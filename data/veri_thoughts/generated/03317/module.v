
module xor4 (
    out,
    a,
    b,
    c,
    d
);

    // Module ports
    output out;
    input a;
    input b;
    input c;
    input d;

    // Module supplies
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    // Local signals
    wire xor1_out;
    wire xor2_out;

    // 2-input XOR gate
    xor xor1 (xor1_out, a, b);

    // 3-input XOR gate
    xor xor2 (xor2_out, c, d, xor1_out);

    // Output assignment
    assign out = xor2_out;

endmodule