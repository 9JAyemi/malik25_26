module math_ops_sva(
    input logic clk,
    input logic reset,
    input logic [1:0] cos,
    input logic [1:0] one,
    input logic [1:0] s1,
    input logic [1:0] s2,
    output logic [1:0] s1_out,
    output logic [1:0] s2_out
);
    // Sequential logic assertions

    // s1_out is the result of adding x2 and x3
    s1_out_calc: assert property (
        @(posedge clk) disable iff (!reset) s1_out == (x2 + x3)
    );

    // s2_out is the result of adding x6 and x7
    s2_out_calc: assert property (
        @(posedge clk) disable iff (!reset) s2_out == (x6 + x7)
    );

    // Intermediate signals x2 and x3 are calculated correctly
    x2_calc: assert property (
        @(posedge clk) disable iff (!reset) x2 == (cos * s2)
    );

    x3_calc: assert property (
        @(posedge clk) disable iff (!reset) x3 == (cos * s1)
    );

    // Intermediate signals x6 and x7 are calculated correctly
    x6_calc: assert property (
        @(posedge clk) disable iff (!reset) x6 == ((1 - cos) * s1)
    );

    x7_calc: assert property (
        @(posedge clk) disable iff (!reset) x7 == (cos * s2)
    );

    // Reset behavior: s1_out and s2_out should be 0 at reset
    reset_s1_out: assert property (
        @(posedge clk) disable iff (!reset) reset |-> s1_out == 2'b00
    );

    reset_s2_out: assert property (
        @(posedge clk) disable iff (!reset) reset |-> s2_out == 2'b00
    );

    // Combinational logic assertions (using clocked assertions for sequential logic)

    // Adder outputs are calculated correctly
    add1_out_calc: assert property (
        @(posedge clk) disable iff (!reset) add1 == (cos + one)
    );

    sub5_out_calc: assert property (
        @(posedge clk) disable iff (!reset) sub5 == (one - cos)
    );

    // Multiplier outputs are calculated correctly
    x2_out_calc: assert property (
        @(posedge clk) disable iff (!reset) x2 == (cos * s2)
    );

    x3_out_calc: assert property (
        @(posedge clk) disable iff (!reset) x3 == (cos * s1)
    );

    x6_out_calc: assert property (
        @(posedge clk) disable iff (!reset) x6 == ((1 - cos) * s1)
    );

    x7_out_calc: assert property (
        @(posedge clk) disable iff (!reset) x7 == (cos * s2)
    );
endmodule