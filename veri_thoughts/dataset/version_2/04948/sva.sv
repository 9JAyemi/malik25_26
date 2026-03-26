module my_module_sva (
    input logic clk,
    input logic out_signal,
    input logic in_signal_1,
    input logic in_signal_2,
    input logic in_signal_3,
    input logic in_signal_4,
    input logic in_signal_5
);

    // Output equals the five-input AND of all inputs.
    check_out_matches_and: assert property (
        @(posedge clk)
        out_signal == (in_signal_1 & in_signal_2 & in_signal_3 & in_signal_4 & in_signal_5)
    );

    // A HIGH output requires all inputs to be HIGH.
    check_out_high_requires_all_inputs_high: assert property (
        @(posedge clk)
        out_signal |-> (in_signal_1 && in_signal_2 && in_signal_3 && in_signal_4 && in_signal_5)
    );

    // All inputs HIGH drives the output HIGH.
    check_all_inputs_high_drive_output_high: assert property (
        @(posedge clk)
        (in_signal_1 && in_signal_2 && in_signal_3 && in_signal_4 && in_signal_5) |-> out_signal
    );

    // A LOW on input 1 forces the output LOW.
    check_input1_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal_1 |-> !out_signal
    );

    // A LOW on input 2 forces the output LOW.
    check_input2_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal_2 |-> !out_signal
    );

    // A LOW on input 3 forces the output LOW.
    check_input3_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal_3 |-> !out_signal
    );

    // A LOW on input 4 forces the output LOW.
    check_input4_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal_4 |-> !out_signal
    );

    // A LOW on input 5 forces the output LOW.
    check_input5_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal_5 |-> !out_signal
    );

endmodule