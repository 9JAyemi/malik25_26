module sky130_fd_sc_lp__a311o_0_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // X must match the implemented five-input AND.
    check_output_matches_five_input_and: assert property (
        @(posedge clk) X === (A1 & A2 & A3 & B1 & C1)
    );

    // All HIGH inputs must drive X HIGH.
    check_all_inputs_high_drive_output_high: assert property (
        @(posedge clk) (A1 && A2 && A3 && B1 && C1) |-> (X === 1'b1)
    );

    // A HIGH output requires all inputs to be HIGH.
    check_output_high_requires_all_inputs_high: assert property (
        @(posedge clk) (X === 1'b1) |-> (A1 && A2 && A3 && B1 && C1)
    );

    // A1 LOW must force X LOW.
    check_a1_low_drives_output_low: assert property (
        @(posedge clk) (!A1) |-> (X === 1'b0)
    );

    // A2 LOW must force X LOW.
    check_a2_low_drives_output_low: assert property (
        @(posedge clk) (!A2) |-> (X === 1'b0)
    );

    // A3 LOW must force X LOW.
    check_a3_low_drives_output_low: assert property (
        @(posedge clk) (!A3) |-> (X === 1'b0)
    );

    // B1 LOW must force X LOW.
    check_b1_low_drives_output_low: assert property (
        @(posedge clk) (!B1) |-> (X === 1'b0)
    );

    // C1 LOW must force X LOW.
    check_c1_low_drives_output_low: assert property (
        @(posedge clk) (!C1) |-> (X === 1'b0)
    );

endmodule