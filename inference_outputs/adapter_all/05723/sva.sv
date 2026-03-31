module mux_add_sub_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic select_ctrl,
    input logic add_sub_ctrl,
    input logic [3:0] Q
);
    // Q equals the low 4 bits of (a + b) when add_sub_ctrl is 1.
    check_q_add_low4: assert property (
        @(posedge add_sub_ctrl or negedge add_sub_ctrl or posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3] or posedge a[4] or negedge a[4] or posedge a[5] or negedge a[5] or posedge a[6] or negedge a[6] or posedge a[7] or negedge a[7] or posedge b[0] or negedge b[0] or posedge b[1] or negedge b[1] or posedge b[2] or negedge b[2] or posedge b[3] or negedge b[3] or posedge b[4] or negedge b[4] or posedge b[5] or negedge b[5] or posedge b[6] or negedge b[6] or posedge b[7] or negedge b[7])
        (Q == (add_sub_ctrl ? (a + b)[3:0] : 4'h0))
    );

    // Q equals the low 4 bits of (a - b) when add_sub_ctrl is 0.
    check_q_sub_low4: assert property (
        @(posedge add_sub_ctrl or negedge add_sub_ctrl or posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3] or posedge a[4] or negedge a[4] or posedge a[5] or negedge a[5] or posedge a[6] or negedge a[6] or posedge a[7] or negedge a[7] or posedge b[0] or negedge b[0] or posedge b[1] or negedge b[1] or posedge b[2] or negedge b[2] or posedge b[3] or negedge b[3] or posedge b[4] or negedge b[4] or posedge b[5] or negedge b[5] or posedge b[6] or negedge b[6] or posedge b[7] or negedge b[7])
        (Q == (add_sub_ctrl ? 4'h0 : (a - b)[3:0]))
    );

    // When add_sub_ctrl is 0, Q is zero.
    check_q_zero_when_add0: assert property (
        @(posedge add_sub_ctrl or negedge add_sub_ctrl or posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3] or posedge a[4] or negedge a[4] or posedge a[5] or negedge a[5] or posedge a[6] or negedge a[6] or posedge a[7] or negedge a[7] or posedge b[0] or negedge b[0] or posedge b[1] or negedge b[1] or posedge b[2] or negedge b[2] or posedge b[3] or negedge b[3] or posedge b[4] or negedge b[4] or posedge b[5] or negedge b[5] or posedge b[6] or negedge b[6] or posedge b[7] or negedge b[7])
        (!add_sub_ctrl) |-> (Q == 4'h0)
    );

    // When add_sub_ctrl is 1, Q equals the low 4 bits of (a + b).
    check_q_add_when_add1: assert property (
        @(posedge add_sub_ctrl or negedge add_sub_ctrl or posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3] or posedge a[4] or negedge a[4] or posedge a[5] or negedge a[5] or posedge a[6] or negedge a[6] or posedge a[7] or negedge a[7] or posedge b[0] or negedge b[0] or posedge b[1] or negedge b[1] or posedge b[2] or negedge b[2] or posedge b[3] or negedge b[3] or posedge b[4] or negedge b[4] or posedge b[5] or negedge b[5] or posedge b[6] or negedge b[6] or posedge b[7] or negedge b[7])
        add_sub_ctrl |-> (Q == (a + b)[3:0])
    );

    // If add_sub_ctrl and a[3:0] are stable, Q remains stable.
    check_q_stable_when_add1_and_a_low_stable: assert property (
        @(posedge add_sub_ctrl or negedge add_sub_ctrl or posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3] or posedge a[4] or negedge a[4] or posedge a[5] or negedge a[5] or posedge a[6] or negedge a[6] or posedge a[7] or negedge a[7] or posedge b[0] or negedge b[0] or posedge b[1] or negedge b[1] or posedge b[2] or negedge b[2] or posedge b[3] or negedge b[3] or posedge b[4] or negedge b[4] or posedge b[5] or negedge b[5] or posedge b[6] or negedge b[6] or posedge b[7] or negedge b[7])
        (add_sub_ctrl && $stable(add_sub_ctrl) && $stable(a[3:0])) |-> $stable(Q)
    );

    // If add_sub_ctrl and b[3:0] are stable, Q remains stable.
    check_q_stable_when_add1_and_b_low_stable: assert property (
        @(posedge add_sub_ctrl or negedge add_sub_ctrl or posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3] or posedge a[4] or negedge a[4] or posedge a[5] or negedge a[5] or posedge a[6] or negedge a[6] or posedge a[7] or negedge a[7] or posedge b[0] or negedge b[0] or posedge b[1] or negedge b[1] or posedge b[2] or negedge b[2] or posedge b[3] or negedge b[3] or posedge b[4] or negedge b[4] or posedge b[5] or negedge b[5] or posedge b[6] or negedge b[6] or posedge b[7] or negedge b[7])
        (add_sub_ctrl && $stable(add_sub_ctrl) && $stable(b[3:0])) |-> $stable(Q)
    );

    // If add_sub_ctrl is 0 and a[3:0], b[3:0] are stable, Q remains stable.
    check_q_stable_when_add0_and_ab_low_stable: assert property (
        @(posedge add_sub_ctrl or negedge add_sub_ctrl or posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3] or posedge a[4] or negedge a[4] or posedge a[5] or negedge a[5] or posedge a[6] or negedge a[6] or posedge a[7] or negedge a[7] or posedge b[0] or negedge b[0] or posedge b[1] or negedge b[1] or posedge b[2] or negedge b[2] or posedge b[3] or negedge b[3] or pos