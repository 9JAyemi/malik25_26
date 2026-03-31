module and_gate(
    input [99:0] in,
    output out_and
);
    assign out_and = &in;
endmodule

module or_gate(
    input [99:0] in,
    output out_or
);
    assign out_or = |in;
endmodule

module xor_gate(
    input [99:0] in,
    output out_xor
);
    assign out_xor = ^in;
endmodule

module top_module( 
    input [99:0] in,
    output out_and,
    output out_or,
    output out_xor 
);
    and_gate and_inst(
        .in(in),
        .out_and(out_and)
    );
    
    or_gate or_inst(
        .in(in),
        .out_or(out_or)
    );
    
    xor_gate xor_inst(
        .in(in),
        .out_xor(out_xor)
    );
endmodule