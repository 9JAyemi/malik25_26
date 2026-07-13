module sky130_fd_sc_hvl__inv_sva (
    input logic A,
    input logic Y
);

    // Y always reflects the inversion of A.
    check_inverter_function: assert property (
        @($global_clock) Y === (~A)
    );

    // A low input produces a high output.
    check_low_input_high_output: assert property (
        @($global_clock) (A == 1'b0) |-> (Y == 1'b1)
    );

    // A high input produces a low output.
    check_high_input_low_output: assert property (
        @($global_clock) (A == 1'b1) |-> (Y == 1'b0)
    );

endmodule