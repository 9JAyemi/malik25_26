module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    input [7:0] c,
    input [7:0] d,
    output [7:0] out1,
    output [7:0] out2
);

    wire [15:0] sum;
    wire gt, lt, eq;
    
    comparator_8bit comp (
        .a(sum[7:0]),
        .b(8'h55),
        .gt(gt),
        .lt(lt),
        .eq(eq)
    );
    
    adder_16bit add (
        .a({8'b0, a}),
        .b({8'b0, b}),
        .sum(sum)
    );
    
    assign out1 = (gt) ? sum[7:0] : (lt) ? c : (eq) ? a : 8'b0;
    assign out2 = (gt) ? 8'b0 : (lt) ? d : (eq) ? b : 8'b0;

endmodule

module comparator_8bit (
    input [7:0] a,
    input [7:0] b,
    output gt,
    output lt,
    output eq
);

    assign gt = (a > b);
    assign lt = (a < b);
    assign eq = (a == b);

endmodule

module adder_16bit (
    input [15:0] a,
    input [15:0] b,
    output [15:0] sum
);

    assign sum = a + b;

endmodule