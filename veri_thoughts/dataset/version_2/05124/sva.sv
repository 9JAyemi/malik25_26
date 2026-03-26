module and_gate_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic out
);

    // RTL has no clock or reset; assertions are sampled on an external clock.

    // Output must match the RTL equation.
    check_output_equation: assert property (
        @(posedge clk) out == (in1 & ~in2)
    );

    // Output high requires in1 high and in2 low.
    check_output_high_inputs: assert property (
        @(posedge clk) out |-> (in1 & ~in2)
    );

    // in1 high with in2 low must drive output high.
    check_true_minterm: assert property (
        @(posedge clk) (in1 & ~in2) |-> out
    );

    // in2 high must force output low.
    check_in2_blocks_output: assert property (
        @(posedge clk) in2 |-> !out
    );

    // in1 low must force output low.
    check_in1_low_forces_output_low: assert property (
        @(posedge clk) !in1 |-> !out
    );

endmodule