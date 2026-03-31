
module top_module (
    input wire [15:0] in,
    input wire [7:0] a,
    input wire [7:0] b,
    output wire [7:0] out
);

    wire [15:0] mult_out;
    wire [7:0] out_hi, out_lo;
    wire [7:0] add_out;

    multiplication mult_inst(
        .a(a),
        .b(b),
        .product(mult_out)
    );

    byte_splitter byte_inst(
        .in(mult_out),
        .out_hi(out_hi),
        .out_lo(out_lo)
    );

    add_overflow_detection add_inst(
        .a(out_hi),
        .b(out_lo),
        .sum(add_out)
    );

    assign out = add_out;

endmodule

module byte_splitter (
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);
    assign out_hi = in[15:8];
    assign out_lo = in[7:0];
endmodule

module add_overflow_detection (
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum,
    output overflow
);
    assign {overflow, sum} = a + b; // Corrected the assignment to use vector concatenation
endmodule

module multiplication (
    input [7:0] a,
    input [7:0] b,
    output [15:0] product
);
    assign product = a * b; // Corrected the assignment to use multiplication operator
endmodule
