module and4_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic e,
    input logic x
);

    // x must equal the AND of all five inputs.
    check_output_exact_and: assert property (
        @(posedge clk) x == (a & b & c & d & e)
    );

    // If all inputs are high, x must be high.
    check_all_inputs_high_drives_x_high: assert property (
        @(posedge clk) (a && b && c && d && e) |-> x
    );

    // If x is high, all inputs must be high.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk) x |-> (a && b && c && d && e)
    );

    // If a is low, x must be low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) !a |-> !x
    );

    // If b is low, x must be low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !b |-> !x
    );

    // If c is low, x must be low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !c |-> !x
    );

    // If d is low, x must be low.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) !d |-> !x
    );

    // If e is low, x must be low.
    check_e_low_forces_x_low: assert property (
        @(posedge clk) !e |-> !x
    );

endmodule