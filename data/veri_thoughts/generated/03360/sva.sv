module d_flip_flop_with_en_and_reset_assertions (
    input logic D,
    input logic C,
    input logic E,
    input logic R,
    input logic Q
);

    // Reset clears Q on the clock edge.
    check_reset_clears_q: assert property (
        @(posedge C) R |=> (Q == 1'b0)
    );

    // When enabled outside reset, Q captures D on the clock edge.
    check_enable_captures_d: assert property (
        @(posedge C) disable iff (R) E |=> (Q == $past(D))
    );

    // When disabled outside reset, Q holds its previous value.
    check_disable_holds_q: assert property (
        @(posedge C) disable iff (R) !E |=> (Q == $past(Q))
    );

endmodule