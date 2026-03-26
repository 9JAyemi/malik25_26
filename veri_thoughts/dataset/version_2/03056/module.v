module bitwise_and(
    input [31:0] a,
    input [31:0] b,
    output [31:0] out
);

    wire [31:0] carry;
    wire [31:0] g;
    wire [31:0] p;

    assign g = a & b;
    assign p = a | b;
    
    assign carry[0] = g[0];
    assign out[0] = g[0];

    genvar i;
    generate
        for (i = 1; i < 32; i = i + 1) begin
            assign carry[i] = g[i] | (p[i] & carry[i-1]);
            assign out[i] = g[i] ^ (p[i] & carry[i-1]);
        end
    endgenerate

endmodule

module control_logic(
    input [31:0] a,
    input [31:0] b,
    input enable,
    output [31:0] out
);

    wire [31:0] result;

    bitwise_and and1(a, b, result);

    assign out = enable ? result : 0;

endmodule

module top_module( 
    input [31:0] a, b,
    input enable,
    output [31:0] out
);

    wire [31:0] result;

    control_logic ctrl(a, b, enable, result);

    assign out = result;

endmodule