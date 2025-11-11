
module my_logic_op (
    input [2:0] in,
    output out
);

    wire [1:0] and_out;
    wire and0_out;
    wire and1_out;
    wire and2_out;
    wire or0_out;
    wire or1_out;
    wire not0_out;
    wire not1_out;
    wire not2_out;
    wire xor0_out;
    wire xor1_out;
    wire xor2_out;
    wire xor3_out;
    wire xor4_out;
    wire xor5_out;
    wire xor6_out;

    // AND gates
    and and0 (and0_out, in[0], in[1]);
    and and1 (and1_out, in[0], in[2]);
    and and2 (and2_out, in[1], in[2]);

    // XOR gates
    xor xor0 (xor0_out, in[0], in[1]);
    xor xor1 (xor1_out, in[0], in[2]);
    xor xor2 (xor2_out, in[1], in[2]);
    xor xor3 (xor3_out, xor0_out, in[2]);
    xor xor4 (xor4_out, xor1_out, in[1]);
    xor xor5 (xor5_out, xor2_out, in[0]);
    xor xor6 (xor6_out, xor3_out, xor4_out, xor5_out);

    // OR gates
    or or0 (or0_out, and0_out, and1_out);
    or or1 (or1_out, or0_out, and2_out, xor6_out);

    // NOT gates
    not not0 (not0_out, in[0]);
    not not1 (not1_out, in[1]);
    not not2 (not2_out, in[2]);

    // Final output
    assign out = (not1_out & not2_out & or1_out ) | (not0_out & not2_out & or1_out ) | (not0_out & not1_out & or1_out) | (not0_out & not1_out & not2_out);

endmodule