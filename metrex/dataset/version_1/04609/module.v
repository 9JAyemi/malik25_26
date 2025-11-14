
module top_module( 
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not
);

    wire [2:0] out_and, not_a, not_b; // Declaring intermediate signals as a wire

    // Instantiate AND_gate module
    AND_gate and_gate_inst (
        .a(a),
        .b(b),
        .out(out_and) 
    );
    
    // Instantiate NOT_gate module for a
    NOT_gate not_gate_a_inst (
        .a(a),
        .out(not_a) 
    );
    
    // Instantiate NOT_gate module for b
    NOT_gate not_gate_b_inst (
        .a(b),
        .out(not_b) 
    );
    
    // Bitwise OR of a and b
    assign out_or_bitwise = a | b;
    
    // Logical OR of a and b
    assign out_or_logical = (a != 0) || (b != 0);
    
    // Inverse of b in the upper half of out_not (bits [5:3])
    assign out_not[5:3] = ~b;
    
    // Inverse of a in the lower half of out_not
    assign out_not[2:0] = ~a;
    
endmodule
module AND_gate (
    input [2:0] a,
    input [2:0] b,
    output [2:0] out
);
    assign out = a & b;
endmodule
module NOT_gate (
    input [2:0] a,
    output [2:0] out
);
    assign out = ~a;
endmodule