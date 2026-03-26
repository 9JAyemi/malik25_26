module shift_register_sva (
    input logic       CLK,
    input logic       LOAD,
    input logic [3:0] D,
    input logic       SHIFT,
    input logic [3:0] Q,
    input logic [3:0] Qbar
);

    // LOAD captures D into Q on the next clock.
    check_load_captures_q: assert property (
        @(posedge CLK) LOAD |=> (Q == $past(D))
    );

    // LOAD captures bitwise-inverted D into Qbar on the next clock.
    check_load_captures_qbar: assert property (
        @(posedge CLK) LOAD |=> (Qbar == ~$past(D))
    );

    // SHIFT moves Q[2:0] into Q[3:1] when LOAD is low.
    check_shift_moves_q_upper_bits: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |=> (Q[3:1] == $past(Q[2:0]))
    );

    // SHIFT inserts 0 into Q[0] when LOAD is low.
    check_shift_inserts_zero_into_q_lsb: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |=> (Q[0] == 1'b0)
    );

    // SHIFT moves Qbar[2:0] into Qbar[3:1] when LOAD is low.
    check_shift_moves_qbar_upper_bits: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |=> (Qbar[3:1] == $past(Qbar[2:0]))
    );

    // SHIFT inserts 1 into Qbar[0] when LOAD is low.
    check_shift_inserts_one_into_qbar_lsb: assert property (
        @(posedge CLK) (!LOAD && SHIFT) |=> (Qbar[0] == 1'b1)
    );

    // With neither LOAD nor SHIFT, Q holds its value.
    check_q_holds_when_idle: assert property (
        @(posedge CLK) (!LOAD && !SHIFT) |=> (Q == $past(Q))
    );

    // With neither LOAD nor SHIFT, Qbar holds its value.
    check_qbar_holds_when_idle: assert property (
        @(posedge CLK) (!LOAD && !SHIFT) |=> (Qbar == $past(Qbar))
    );

endmodule