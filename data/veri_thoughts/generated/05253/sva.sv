module tff_mux_assertions (
    input logic       clk,
    input logic       d,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [3:0] q
);

    // q[0] reflects the prior-cycle d value.
    check_q0_tracks_prev_d: assert property (
        @(posedge clk) disable iff ($initstate) q[0] == $past(d)
    );

    // q either holds its value or bitwise inverts on each clock.
    check_q_holds_or_inverts: assert property (
        @(posedge clk) disable iff ($initstate) (q == $past(q)) || (q == ~$past(q))
    );

    // q holds when prior q[0] matched prior d.
    check_hold_when_prev_q0_matches_prev_d: assert property (
        @(posedge clk) disable iff ($initstate) ($past(q[0]) == $past(d)) |-> (q == $past(q))
    );

    // q inverts when prior q[0] differed from prior d.
    check_invert_when_prev_q0_differs_prev_d: assert property (
        @(posedge clk) disable iff ($initstate) ($past(q[0]) != $past(d)) |-> (q == ~$past(q))
    );

    // Any observed change in q is a full bitwise inversion.
    check_change_is_full_inversion: assert property (
        @(posedge clk) disable iff ($initstate) (q != $past(q)) |-> (q == ~$past(q))
    );

    // No observed change in q means prior q[0] matched prior d.
    check_hold_only_when_prev_q0_matches_prev_d: assert property (
        @(posedge clk) disable iff ($initstate) (q == $past(q)) |-> ($past(q[0]) == $past(d))
    );

    // With prior d low and prior q[0] low, q holds.
    check_d0_q0_0_holds: assert property (
        @(posedge clk) disable iff ($initstate) ($past(d) == 1'b0 && $past(q[0]) == 1'b0) |-> (q == $past(q))
    );

    // With prior d low and prior q[0] high, q inverts.
    check_d0_q0_1_inverts: assert property (
        @(posedge clk) disable iff ($initstate) ($past(d) == 1'b0 && $past(q[0]) == 1'b1) |-> (q == ~$past(q))
    );

    // With prior d high and prior q[0] low, q inverts.
    check_d1_q0_0_inverts: assert property (
        @(posedge clk) disable iff ($initstate) ($past(d) == 1'b1 && $past(q[0]) == 1'b0) |-> (q == ~$past(q))
    );

    // With prior d high and prior q[0] high, q holds.
    check_d1_q0_1_holds: assert property (
        @(posedge clk) disable iff ($initstate) ($past(d) == 1'b1 && $past(q[0]) == 1'b1) |-> (q == $past(q))
    );

endmodule