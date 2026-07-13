module and4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // X must equal the 4-input AND of A, B, C, and D.
    check_x_matches_and4: assert property (
        @(posedge clk) X === (A & B & C & D)
    );

    // If all inputs are high, X must be high.
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk)
        ((A === 1'b1) && (B === 1'b1) && (C === 1'b1) && (D === 1'b1)) |-> (X === 1'b1)
    );

    // If any input is low, X must be low.
    check_any_low_input_drives_x_low: assert property (
        @(posedge clk)
        ((A === 1'b0) || (B === 1'b0) || (C === 1'b0) || (D === 1'b0)) |-> (X === 1'b0)
    );

    // A high X requires all inputs to be high.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk)
        (X === 1'b1) |-> ((A === 1'b1) && (B === 1'b1) && (C === 1'b1) && (D === 1'b1))
    );

endmodule