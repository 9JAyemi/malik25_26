module sky130_fd_sc_ms__nor3_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);

    // Y matches the 3-input NOR of A, B, and C.
    check_nor_function: assert property (
        @($global_clock) Y == ~(A | B | C)
    );

    // All low inputs drive Y high.
    check_all_inputs_low_drives_high: assert property (
        @($global_clock) (!A && !B && !C) |-> (Y == 1'b1)
    );

    // A high forces Y low.
    check_a_high_drives_low: assert property (
        @($global_clock) A |-> (Y == 1'b0)
    );

    // B high forces Y low.
    check_b_high_drives_low: assert property (
        @($global_clock) B |-> (Y == 1'b0)
    );

    // C high forces Y low.
    check_c_high_drives_low: assert property (
        @($global_clock) C |-> (Y == 1'b0)
    );

    // Y high implies all three inputs are low.
    check_y_high_requires_all_inputs_low: assert property (
        @($global_clock) Y |-> (!A && !B && !C)
    );

endmodule