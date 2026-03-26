module mux_add_sub_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic select_ctrl,
    input logic add_sub_ctrl,
    input logic [3:0] Q,
    input logic [7:0] add_sub_out,
    input logic mux_enable
);

    // add_sub_out is the 8-bit sum when add_sub_ctrl is high.
    check_add_sub_out_add_mode: assert property (
        @($global_clock) add_sub_ctrl |-> (add_sub_out == (a + b))
    );

    // add_sub_out is the 8-bit difference when add_sub_ctrl is low.
    check_add_sub_out_sub_mode: assert property (
        @($global_clock) !add_sub_ctrl |-> (add_sub_out == (a - b))
    );

    // mux_enable directly follows add_sub_ctrl.
    check_mux_enable_tracks_ctrl: assert property (
        @($global_clock) (mux_enable == add_sub_ctrl)
    );

    // Q passes the low nibble of add_sub_out when enabled.
    check_q_matches_add_sub_out_when_enabled: assert property (
        @($global_clock) mux_enable |-> (Q == add_sub_out[3:0])
    );

    // Q is forced low when the mux is disabled.
    check_q_zero_when_disabled: assert property (
        @($global_clock) !mux_enable |-> (Q == 4'h0)
    );

    // Changing select_ctrl alone does not affect Q.
    check_select_ctrl_unused_for_q: assert property (
        @($global_clock) $changed(select_ctrl) && $stable(a) && $stable(b) && $stable(add_sub_ctrl) |-> $stable(Q)
    );

endmodule

bind mux_add_sub mux_add_sub_sva i_mux_add_sub_sva (
    .a(a),
    .b(b),
    .select_ctrl(select_ctrl),
    .add_sub_ctrl(add_sub_ctrl),
    .Q(Q),
    .add_sub_out(add_sub_out),
    .mux_enable(mux_enable)
);