module mux_add_sub_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic select_ctrl,
    input logic add_sub_ctrl,
    input logic [3:0] Q
);

    // Q must always match the selected 4-bit output.
    check_q_matches_selected_output: assert property (
        @($global_clock)
        Q == (add_sub_ctrl ? a[3:0] : 4'h0)
    );

    // In add mode, Q must equal the low 4 bits of a.
    check_add_mode_selects_a_low_nibble: assert property (
        @($global_clock)
        add_sub_ctrl |-> (Q == a[3:0])
    );

    // In subtract mode, Q must be zero.
    check_sub_mode_selects_zero: assert property (
        @($global_clock)
        !add_sub_ctrl |-> (Q == 4'h0)
    );

endmodule