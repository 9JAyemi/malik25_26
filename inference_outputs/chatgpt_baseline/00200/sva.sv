module sky130_fd_sc_hd__nor4_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must equal the 4-input NOR of A, B, C, and D.
    check_nor_function: assert property (
        @($global_clock) Y == !(A || B || C || D)
    );

    // If all inputs are low, Y must be high.
    check_all_inputs_low_drive_high: assert property (
        @($global_clock) (!A && !B && !C && !D) |-> Y
    );

    // If any input is high, Y must be low.
    check_any_input_high_drives_low: assert property (
        @($global_clock) (A || B || C || D) |-> !Y
    );

    // A high forces the NOR output low.
    check_a_high_drives_low: assert property (
        @($global_clock) A |-> !Y
    );

    // B high forces the NOR output low.
    check_b_high_drives_low: assert property (
        @($global_clock) B |-> !Y
    );

    // C high forces the NOR output low.
    check_c_high_drives_low: assert property (
        @($global_clock) C |-> !Y
    );

    // D high forces the NOR output low.
    check_d_high_drives_low: assert property (
        @($global_clock) D |-> !Y
    );

    // A high Y implies all four inputs are low.
    check_output_high_requires_all_inputs_low: assert property (
        @($global_clock) Y |-> (!A && !B && !C && !D)
    );

    // A low Y implies at least one input is high.
    check_output_low_requires_some_input_high: assert property (
        @($global_clock) !Y |-> (A || B || C || D)
    );

endmodule