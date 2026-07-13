module counter_4bit_sync_reset_sva (
    input logic       CK,
    input logic       RST,
    input logic [3:0] Q
);

    // Synchronous reset forces Q to zero by the next clock sample.
    check_reset_clears_counter: assert property (
        @(posedge CK) RST |=> (Q == 4'b0000)
    );

    // Without reset in consecutive cycles, the counter advances by one modulo 16.
    check_counter_advances_when_running: assert property (
        @(posedge CK) disable iff (RST)
        !$past(RST) |-> (Q == ($past(Q) + 4'd1))
    );

    // On reset assertion, sampled Q still reflects the previous non-reset increment.
    check_last_count_visible_on_reset_assertion: assert property (
        @(posedge CK)
        (RST && !$past(RST)) |-> (Q == ($past(Q) + 4'd1))
    );

endmodule