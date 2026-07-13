module my_and4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X must equal the AND of all four inputs.
    check_output_definition: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

    // If all inputs are high, X must be high.
    check_all_high_drives_x_high: assert property (
        @(posedge clk) (A & B & C & D) |-> X
    );

    // If X is high, all inputs must be high.
    check_x_high_requires_all_high: assert property (
        @(posedge clk) X |-> (A & B & C & D)
    );

    // A low input forces X low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) (!A) |-> (!X)
    );

    // A low input forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) (!B) |-> (!X)
    );

    // A low input forces X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) (!C) |-> (!X)
    );

    // A low input forces X low.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) (!D) |-> (!X)
    );

    // If X is low, at least one input must be low.
    check_x_low_requires_some_input_low: assert property (
        @(posedge clk) (!X) |-> ((!A) | (!B) | (!C) | (!D))
    );

endmodule