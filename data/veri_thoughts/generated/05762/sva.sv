module Hyperbolic_Functions_sva (
    input logic clk,
    input logic [2:0] x,
    input logic [15:0] sineh,
    input logic [15:0] cosh,
    input logic [15:0] tanh
);

    // x=0 maps to sineh=0, cosh=1, tanh=0.
    check_x0_lookup: assert property (
        @(posedge clk)
        (x == 3'd0) |-> (sineh == 16'd0 && cosh == 16'd1 && tanh == 16'd0)
    );

    // x=1 maps to sineh=1, cosh=1, tanh=1.
    check_x1_lookup: assert property (
        @(posedge clk)
        (x == 3'd1) |-> (sineh == 16'd1 && cosh == 16'd1 && tanh == 16'd1)
    );

    // x=2 maps to sineh=3, cosh=4, tanh=1.
    check_x2_lookup: assert property (
        @(posedge clk)
        (x == 3'd2) |-> (sineh == 16'd3 && cosh == 16'd4 && tanh == 16'd1)
    );

    // x=3 maps to sineh=10, cosh=11, tanh=1.
    check_x3_lookup: assert property (
        @(posedge clk)
        (x == 3'd3) |-> (sineh == 16'd10 && cosh == 16'd11 && tanh == 16'd1)
    );

    // x=4 maps to sineh=27, cosh=28, tanh=1.
    check_x4_lookup: assert property (
        @(posedge clk)
        (x == 3'd4) |-> (sineh == 16'd27 && cosh == 16'd28 && tanh == 16'd1)
    );

    // x=5,6,7 take the default mapping of sineh=0, cosh=1, tanh=0.
    check_default_lookup: assert property (
        @(posedge clk)
        (x == 3'd5 || x == 3'd6 || x == 3'd7) |-> (sineh == 16'd0 && cosh == 16'd1 && tanh == 16'd0)
    );

    // tanh is 1 only for inputs 1 through 4.
    check_tanh_region: assert property (
        @(posedge clk)
        ((x == 3'd1 || x == 3'd2 || x == 3'd3 || x == 3'd4) |-> (tanh == 16'd1))
    );

    // tanh is 0 for input 0 and all default cases.
    check_tanh_default_region: assert property (
        @(posedge clk)
        ((x == 3'd0 || x == 3'd5 || x == 3'd6 || x == 3'd7) |-> (tanh == 16'd0))
    );

endmodule