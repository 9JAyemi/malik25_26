module sky130_fd_sc_ls__nand3_assertions (
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);

    // Y must always implement a 3-input NAND.
    check_nand_function: assert property (
        @($global_clock) Y == ~(A & B & C)
    );

    // All three high inputs force Y low.
    check_all_high_drives_low: assert property (
        @($global_clock) (A && B && C) |-> !Y
    );

    // Any low input forces Y high.
    check_any_low_drives_high: assert property (
        @($global_clock) (!A || !B || !C) |-> Y
    );

    // A low output is only possible when all inputs are high.
    check_low_output_requires_all_high: assert property (
        @($global_clock) !Y |-> (A && B && C)
    );

    // A high output implies at least one input is low.
    check_high_output_requires_any_low: assert property (
        @($global_clock) Y |-> (!A || !B || !C)
    );

endmodule