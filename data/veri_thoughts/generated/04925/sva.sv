module sky130_fd_sc_hdll__and4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Output matches the 4-input AND when inputs are known.
    check_and4_function_known_inputs: assert property (
        @(posedge clk) !$isunknown({A, B, C, D}) |-> (X === (A & B & C & D))
    );

    // Output is high when all inputs are high.
    check_output_high_when_all_inputs_high: assert property (
        @(posedge clk) (A === 1'b1 && B === 1'b1 && C === 1'b1 && D === 1'b1) |-> (X === 1'b1)
    );

    // Output is low when any input is low.
    check_output_low_when_any_input_low: assert property (
        @(posedge clk) (A === 1'b0 || B === 1'b0 || C === 1'b0 || D === 1'b0) |-> (X === 1'b0)
    );

    // A high output requires all inputs to be high.
    check_output_high_requires_all_inputs_high: assert property (
        @(posedge clk) (X === 1'b1) |-> (A === 1'b1 && B === 1'b1 && C === 1'b1 && D === 1'b1)
    );

    // A low output with known inputs requires at least one low input.
    check_output_low_requires_low_input_when_inputs_known: assert property (
        @(posedge clk) (!$isunknown({A, B, C, D}) && X === 1'b0) |-> (A === 1'b0 || B === 1'b0 || C === 1'b0 || D === 1'b0)
    );

endmodule