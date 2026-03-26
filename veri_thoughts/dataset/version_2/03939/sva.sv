module six_to_one_sva (
    input logic clk,
    input logic out_signal,
    input logic in_signal1,
    input logic in_signal2,
    input logic in_signal3,
    input logic in_signal4,
    input logic in_signal5,
    input logic in_signal6
);

    // Output must equal the AND of all six inputs.
    check_output_matches_and: assert property (
        @(posedge clk)
        out_signal == (in_signal1 & in_signal2 & in_signal3 & in_signal4 & in_signal5 & in_signal6)
    );

    // A high output requires all six inputs to be high.
    check_output_high_requires_all_inputs_high: assert property (
        @(posedge clk)
        out_signal |-> (in_signal1 & in_signal2 & in_signal3 & in_signal4 & in_signal5 & in_signal6)
    );

    // All six high inputs must drive the output high.
    check_all_inputs_high_drive_output_high: assert property (
        @(posedge clk)
        (in_signal1 & in_signal2 & in_signal3 & in_signal4 & in_signal5 & in_signal6) |-> out_signal
    );

    // A low in_signal1 must force the output low.
    check_input1_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal1 |-> !out_signal
    );

    // A low in_signal2 must force the output low.
    check_input2_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal2 |-> !out_signal
    );

    // A low in_signal3 must force the output low.
    check_input3_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal3 |-> !out_signal
    );

    // A low in_signal4 must force the output low.
    check_input4_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal4 |-> !out_signal
    );

    // A low in_signal5 must force the output low.
    check_input5_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal5 |-> !out_signal
    );

    // A low in_signal6 must force the output low.
    check_input6_low_forces_output_low: assert property (
        @(posedge clk)
        !in_signal6 |-> !out_signal
    );

endmodule