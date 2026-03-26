module shift_register_4bit_sva (
    input logic [3:0] A,
    input logic       LOAD,
    input logic       CLK,
    input logic [3:0] Q
);

    // A high LOAD transfers A into Q on the next sampled cycle.
    check_load_captures_a: assert property (
        @(posedge CLK) LOAD |=> (Q == $past(A))
    );

    // A low LOAD causes Q to retain its previous value.
    check_hold_when_load_low: assert property (
        @(posedge CLK) !LOAD |=> (Q == $past(Q))
    );

    // Q follows the prior cycle's LOAD-controlled update rule.
    check_q_transition_rule: assert property (
        @(posedge CLK) 1'b1 |=> ($past(LOAD) ? (Q == $past(A)) : (Q == $past(Q)))
    );

endmodule