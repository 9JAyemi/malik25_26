module simple_circuit_sva (
    input logic Q,
    input logic C,
    input logic R,
    input logic E,
    input logic D
);

    // A reset assertion clears Q by the next sampled event.
    check_reset_clears_q: assert property (
        @(posedge C or posedge R) $rose(R) |=> (Q == 1'b0)
    );

    // While reset stays asserted, Q remains low.
    check_reset_holds_q_low: assert property (
        @(posedge C or posedge R) (R && $past(R)) |-> (Q == 1'b0)
    );

    // An enabled clock captures D into Q.
    check_enable_captures_d: assert property (
        @(posedge C) disable iff (R) E |=> (Q == $past(D))
    );

    // A disabled clock leaves Q unchanged.
    check_disable_holds_q: assert property (
        @(posedge C) disable iff (R) !E |=> (Q == $past(Q))
    );

endmodule