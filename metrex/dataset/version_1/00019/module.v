module and_gate(
    input a,
    input b,
    input c,
    input d,
    output out
);
    assign out = a & b & c & d;
endmodule

module or_gate(
    input a,
    input b,
    input c,
    input d,
    output out
);
    assign out = a | b | c | d;
endmodule

module xor_gate(
    input a,
    input b,
    output out
);
    assign out = a ^ b;
endmodule

module combined_module(
    input [3:0] in,
    output out
);
    wire and_out;
    wire or_out;
    and_gate and_inst(
        .a(in[0]),
        .b(in[1]),
        .c(in[2]),
        .d(in[3]),
        .out(and_out)
    );
    or_gate or_inst(
        .a(in[0]),
        .b(in[1]),
        .c(in[2]),
        .d(in[3]),
        .out(or_out)
    );
    xor_gate xor_inst(
        .a(and_out),
        .b(or_out),
        .out(out)
    );
endmodule

module top_module( 
    input [3:0] in,
    output out
);
    combined_module combined_inst(
        .in(in),
        .out(out)
    );
endmodule