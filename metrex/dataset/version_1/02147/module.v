
module top_module (
    input [2:0] a,
    input [2:0] b,
    input sel_b1,
    input sel_b2,
    output reg out_always,
    output [2:0] out_or_reg,
    output out_or_logical,
    output [5:0] out_not
);

    // 2-to-1 multiplexer
    always @(*) begin
        out_always <= sel_b1 ? b : a;
    end

    // Bitwise-OR
    assign out_or_reg = a | b;

    // Logical-OR
    assign out_or_logical = (a != 0) || (b != 0);

    // Inverse of both vectors
    assign out_not = ~{a, b};

endmodule
