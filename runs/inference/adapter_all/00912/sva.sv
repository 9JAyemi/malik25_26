module shift_register_4bit_sva (
    input logic CLK,
    input logic LOAD,
    input logic CLR,
    input logic [3:0] D,
    input logic [3:0] Q,
    input logic [3:0] Q_next
);

    // CLR clears both registers on the next cycle.
    check_clear_sets_outputs: assert property (
        @(posedge CLK) CLR |=> (Q == 4'b0000 && Q_next == 4'b0000)
    );

    // LOAD copies D into both registers on the next cycle.
    check_load_copies_d: assert property (
        @(posedge CLK) disable iff (CLR) LOAD |=> (Q == $past(D) && Q_next == $past(D))
    );

    // With LOAD low, Q shifts left and captures D[3] into bit 0.
    check_shift_updates_q: assert property (
        @(posedge CLK) disable iff (CLR) !LOAD |=> (Q == {$past(Q[2:0]), $past(D[3])})
    );

    // With LOAD low, Q_next shifts left and captures D[3] into bit 0.
    check_shift_updates_qnext: assert property (
        @(posedge CLK) disable iff (CLR) !LOAD |=> (Q_next == {$past(Q_next[2:0]), $past(D[3])})
    );

    // CLR overrides LOAD when both are asserted.
    check_clear_priority_over_load: assert property (
        @(posedge CLK) (CLR && LOAD) |=> (Q == 4'b0000 && Q_next == 4'b0000)
    );

endmodule