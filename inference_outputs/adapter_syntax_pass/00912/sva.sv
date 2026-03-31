module shift_register_4bit_sva (
    input logic CLK,
    input logic LOAD,
    input logic CLR,
    input logic [3:0] D,
    input logic [3:0] Q,
    input logic [3:0] Q_next
);

    // CLR forces both outputs to zero on the next clock.
    check_clear_forces_zero: assert property (
        @(posedge CLK) CLR |=> (Q == 4'b0000 && Q_next == 4'b0000)
    );

    // LOAD captures D into both outputs on the next clock.
    check_load_captures_d: assert property (
        @(posedge CLK) disable iff (CLR) LOAD |=> (Q == $past(D) && Q_next == $past(D))
    );

    // Without LOAD, Q shifts left and inserts D[3] into bit 0.
    check_shift_updates_q: assert property (
        @(posedge CLK) disable iff (CLR) !LOAD |=> (Q == { $past(Q[2:0]), $past(D[3]) })
    );

    // Without LOAD, Q_next shifts left and inserts D[3] into bit 0.
    check_shift_updates_qnext: assert property (
        @(posedge CLK) disable iff (CLR) !LOAD |=> (Q_next == { $past(Q_next[2:0]), $past(D[3]) })
    );

    // CLR has priority over LOAD when both are asserted.
    check_clear_overrides_load: assert property (
        @(posedge CLK) (CLR && LOAD) |=> (Q == 4'b0000 && Q_next == 4'b0000)
    );

endmodule