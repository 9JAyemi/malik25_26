module shift_register_4bit_sva (
    input logic CLK,
    input logic LOAD,
    input logic CLR,
    input logic [3:0] D,
    input logic [3:0] Q,
    input logic [3:0] Q_next
);
    // Clock: CLK (posedge). Reset: CLR synchronous active-high. Sequential-only logic.
    // Behavior: on posedge CLK: if CLR->0; else if LOAD->D; else shift left with D[3] into Q[0].

    // Q implements the exact next-state function.
    check_q_next_state: assert property (
        @(posedge CLK) disable iff ($initstate)
            Q == (CLR ? 4'b0000 : (LOAD ? D : { $past(Q[2:0]), D[3] }))
    );

    // Q_next implements the same next-state function.
    check_qnext_next_state: assert property (
        @(posedge CLK) disable iff ($initstate)
            Q_next == (CLR ? 4'b0000 : (LOAD ? D : { $past(Q[2:0]), D[3] }))
    );

    // Q_next always mirrors Q each cycle.
    check_qnext_mirrors_q: assert property (
        @(posedge CLK) disable iff ($initstate)
            (Q_next == Q)
    );

    // On shift (no CLR, no LOAD), Q[3:1] take prior Q[2:0].
    check_shift_upper_bits_q: assert property (
        @(posedge CLK) disable iff (CLR || $initstate)
            (!LOAD) |-> (Q[3] == $past(Q[2]) && Q[2] == $past(Q[1]) && Q[1] == $past(Q[0]))
    );

    // On shift, Q[0] takes current D[3].
    check_shift_lsb_from_d3_q: assert property (
        @(posedge CLK) disable iff (CLR || $initstate)
            (!LOAD) |-> (Q[0] == D[3])
    );

    // On shift (no CLR, no LOAD), Q_next[3:1] take prior Q[2:0].
    check_shift_upper_bits_qnext: assert property (
        @(posedge CLK) disable iff (CLR || $initstate)
            (!LOAD) |-> (Q_next[3] == $past(Q[2]) && Q_next[2] == $past(Q[1]) && Q_next[1] == $past(Q[0]))
    );

    // On shift, Q_next[0] takes current D[3].
    check_shift_lsb_from_d3_qnext: assert property (
        @(posedge CLK) disable iff (CLR || $initstate)
            (!LOAD) |-> (Q_next[0] == D[3])
    );
endmodule