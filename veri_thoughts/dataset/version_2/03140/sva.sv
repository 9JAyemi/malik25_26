module vd12401_sva (
    input logic clk,
    input logic v0e28cb,
    input logic v3ca442,
    input logic vcbab45
);

    // Output must equal the AND of the two inputs.
    check_output_is_and: assert property (
        @(posedge clk) vcbab45 == (v0e28cb & v3ca442)
    );

    // A HIGH output requires both inputs to be HIGH.
    check_high_output_requires_both_inputs_high: assert property (
        @(posedge clk) vcbab45 |-> (v0e28cb && v3ca442)
    );

    // A LOW first input forces the output LOW.
    check_low_first_input_forces_low_output: assert property (
        @(posedge clk) !v0e28cb |-> !vcbab45
    );

    // A LOW second input forces the output LOW.
    check_low_second_input_forces_low_output: assert property (
        @(posedge clk) !v3ca442 |-> !vcbab45
    );

    // Both HIGH inputs force the output HIGH.
    check_both_inputs_high_force_high_output: assert property (
        @(posedge clk) (v0e28cb && v3ca442) |-> vcbab45
    );

endmodule