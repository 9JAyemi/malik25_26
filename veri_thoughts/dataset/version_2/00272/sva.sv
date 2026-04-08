module and2b_sva (
    input logic A_N,
    input logic B,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // X must implement the RTL equation.
    check_boolean_function: assert property (
        @($global_clock) X === (~A_N & B)
    );

    // A_N high forces X low.
    check_a_n_high_forces_x_low: assert property (
        @($global_clock) (A_N === 1'b1) |-> (X === 1'b0)
    );

    // B low forces X low.
    check_b_low_forces_x_low: assert property (
        @($global_clock) (B === 1'b0) |-> (X === 1'b0)
    );

    // A_N low and B high drive X high.
    check_active_inputs_drive_x_high: assert property (
        @($global_clock) ((A_N === 1'b0) && (B === 1'b1)) |-> (X === 1'b1)
    );

    // X high implies the enabling input combination.
    check_x_high_requires_inputs: assert property (
        @($global_clock) (X === 1'b1) |-> ((A_N === 1'b0) && (B === 1'b1))
    );

endmodule