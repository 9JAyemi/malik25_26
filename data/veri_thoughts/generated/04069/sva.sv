module dff_reset_enable_sva (
    input logic D,
    input logic CLK,
    input logic RESET,
    input logic EN,
    input logic Q
);

    // Active-low reset forces Q low.
    check_reset_forces_q_low: assert property (
        @(posedge CLK)
        !RESET |-> (Q == 1'b0)
    );

    // A sampled reset leaves Q low through the next clock sample.
    check_reset_value_persists_to_next_clock: assert property (
        @(posedge CLK)
        !RESET |=> (Q == 1'b0)
    );

    // When enabled, Q captures D on the clock edge.
    check_load_when_enabled: assert property (
        @(posedge CLK) disable iff (!RESET)
        EN |=> (Q == $past(D))
    );

    // When disabled, Q holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (!RESET)
        !EN |=> (Q == $past(Q))
    );

endmodule