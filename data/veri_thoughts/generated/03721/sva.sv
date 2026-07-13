module and2b_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND
);

    // X implements the combinational function (~A) & B.
    check_x_function: assert property (
        @($global_clock) X === ((~A) & B)
    );

    // When B is low, X must be low.
    check_b_low_forces_x_low: assert property (
        @($global_clock) (B === 1'b0) |-> (X === 1'b0)
    );

    // When A is high, X must be low.
    check_a_high_forces_x_low: assert property (
        @($global_clock) (A === 1'b1) |-> (X === 1'b0)
    );

    // When A is low and B is high, X must be high.
    check_a_low_b_high_drives_x_high: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b1)) |-> (X === 1'b1)
    );

    // A high X implies A is low and B is high.
    check_x_high_implies_input_condition: assert property (
        @($global_clock) (X === 1'b1) |-> ((A === 1'b0) && (B === 1'b1))
    );

endmodule