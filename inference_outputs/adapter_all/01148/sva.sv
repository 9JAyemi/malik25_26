module and3b_sva (
    input logic clk,
    input logic A_N,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must match the implemented combinational function.
    check_x_matches_function: assert property (
        @(posedge clk)
        X == ((A_N == 1'b1) && (B == 1'b1) && (C == 1'b1))
    );

    // All three active inputs must drive X high.
    check_all_active_inputs_drive_x_high: assert property (
        @(posedge clk)
        ((A_N == 1'b1) && (B == 1'b1) && (C == 1'b1)) |-> (X == 1'b1)
    );

    // Any low input must drive X low.
    check_any_low_input_drives_x_low: assert property (
        @(posedge clk)
        ((A_N == 1'b0) || (B == 1'b0) || (C == 1'b0)) |-> (X == 1'b0)
    );

    // X high requires all three active inputs.
    check_x_high_requires_all_active_inputs: assert property (
        @(posedge clk)
        (X == 1'b1) |-> ((A_N == 1'b1) && (B == 1'b1) && (C == 1'b1))
    );

    // X low requires at least one low input.
    check_x_low_requires_any_low_input: assert property (
        @(posedge clk)
        (X == 1'b0) |-> ((A_N == 1'b0) || (B == 1'b0) || (C == 1'b0))
    );

    // X must not be high-impedance when all inputs are known.
    check_x_not_x_when_all_inputs_known: assert property (
        @(posedge clk)
        (!$isunknown({A_N, B, C})) |-> (X != 1'bx)
    );

endmodule