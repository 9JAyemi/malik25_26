
module top_module(
    input a,
    input b,
    input c,
    input d,
    output out_final
);

    wire xor1_out;
    wire xor2_out;

    xor_gate xor1(.a(a), .b(b), .out(xor1_out));
    xor_gate xor2(.a(c), .b(d), .out(xor2_out));
    and_gate and1(.a(xor1_out), .b(xor2_out), .out(out_final));

endmodule

module xor_gate(
    input a,
    input b,
    output out
);

    assign out = a ^ b;

endmodule

module and_gate(
    input a,
    input b,
    output out
);

    assign out = a & b;

endmodule
