module top_module( 
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not
);

    // Bitwise-OR module
    bitwise_or_module bitwise_or_inst(
        .a(a),
        .b(b),
        .out(out_or_bitwise)
    );
    
    // Logical-OR module
    assign out_or_logical = |{a,b};
    
    // NOT module
    not_module not_inst(
        .in({a,b}),
        .out(out_not)
    );
    
endmodule

module bitwise_or_module(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out
);

    assign out = a | b;
    
endmodule

module not_module(
    input [5:0] in,
    output [5:0] out
);

    assign out = ~in;
    
endmodule