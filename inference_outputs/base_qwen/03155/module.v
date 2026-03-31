
module math_ops(
    input clk,
    input reset,
    input [1:0] cos,
    input [1:0] one,
    input [1:0] s1,
    input [1:0] s2,
    output [1:0] s1_out,
    output [1:0] s2_out
);

parameter BITS = 2;

// Declare intermediate signals
wire [1:0] add1;
wire [1:0] x2;
wire [1:0] x3;

wire [1:0] sub5;
wire [1:0] x6;
wire [1:0] x7;

// Instantiate modules
Adder add1_add(
    .clk(clk),
    .opa(cos),
    .opb(one),
    .out(add1)
);

Multiplier x2_mul(
    .clk(clk),
    .opa(add1),
    .opb(s2),
    .out(x2)
);

Multiplier x3_mul(
    .clk(clk),
    .opa(cos),
    .opb(s1),
    .out(x3)
);

Adder s1_out_add(
    .clk(clk),
    .opa(x2),
    .opb(x3),
    .out(s1_out)
);

Adder sub5_add(
    .clk(clk),
    .opa(one),
    .opb(cos),
    .out(sub5)
);

Multiplier x6_mul(
    .clk(clk),
    .opa(sub5),
    .opb(s1),
    .out(x6)
);

Multiplier x7_mul(
    .clk(clk),
    .opa(cos),
    .opb(s2),
    .out(x7)
);

Adder s2_out_add(
    .clk(clk),
    .opa(x6),
    .opb(x7),
    .out(s2_out)
);

endmodule

module Adder(
    input clk,
    input [1:0] opa,
    input [1:0] opb,
    output reg [1:0] out
);

always @(posedge clk) begin
    out <= opa + opb;
end
endmodule

module Multiplier(
    input clk,
    input [1:0] opa,
    input [1:0] opb,
    output reg [1:0] out
);

    always @(posedge clk) begin
        out <= opa * opb;
    end
endmodule
