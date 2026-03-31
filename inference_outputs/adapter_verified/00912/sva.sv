module shift_register_4bit_sva (
    input logic CLK,
    input logic LOAD,
    input logic CLR,
    input logic [3:0] D,
    input logic [3:0] Q,
    input logic [3:0] Q_next
);

// CLR clears both Q and Q_next on the next cycle.
    check_clear_sets_outputs: assert property (
        @(posedge CLK) CLR |=> (Q == 4'b0000) && (Q_next == 4'b0000)
    );

// LOAD captures D into both Q and Q_next on the next cycle.
    check_load_captures_d: assert property (
        @(posedge CLK) disable iff (CLR) LOAD |=> (Q == $past(D)) && (Q_next == $past(D))
    );

// Without LOAD, Q_next shifts left by one and takes D[3] into bit 0.
    check_shift_updates_qnext: assert property (
        @(posedge CLK) disable iff (CLR) !LOAD |=> (Q_next == {$past(Q[2:0]), $past(D[3])})
    );

// Without LOAD, Q shifts left by one and takes D[3] into bit 0.
    check_shift_updates_q: assert property (
        @(posedge CLK) disable iff (CLR) !LOAD |=> (Q == {$past(Q[2:0]), $past(D[3])})
    );

// With LOAD, Q_next captures D on the next cycle.
    check_load_captures_d_into_qnext: assert property (
        @(posedge CLK) LOAD |=> (Q_next == $past(D))
    );

// With LOAD, Q captures D on the next cycle.
    check_load_captures_d_into_q: assert property (
        @(posedge CLK) LOAD |=> (Q == $past(D))
    );

// With LOAD, Q_next equals Q on the next cycle.
    check_load_keeps_qnext_equal_q: assert property (
        @(posedge CLK) LOAD |=> (Q_next == Q)
    );

// Without LOAD, Q_next equals Q on the next cycle.
    check_shift_keeps_qnext_equal_q: assert property (
        @(posedge CLK) disable iff (CLR) !LOAD |=> (Q_next == Q)
    );

endmodule
