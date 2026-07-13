module bitwise_or(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out
);
    assign out = a | b;
endmodule

module logical_or(
    input [2:0] a,
    input [2:0] b,
    output out
);
    assign out = (a != 0) || (b != 0);
endmodule

module top_module( 
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not
); 
    wire [2:0] a_not, b_not;
    wire [2:0] or_bitwise;
    
    bitwise_or bitwise_or_inst(
        .a(a),
        .b(b),
        .out(or_bitwise)
    );
    
    logical_or logical_or_inst(
        .a(a),
        .b(b),
        .out(out_or_logical)
    );
    
    assign a_not = ~a;
    assign b_not = ~b;
    
    assign out_not = {b_not, a_not};
    assign out_or_bitwise = or_bitwise;
endmodule