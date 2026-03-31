module counter_4bit_sync_reset_sva (
    input logic CK,
    input logic RST,
    input logic [3:0] Q
);

    // Reset drives Q to zero on the next clock.
    check_reset_clears_q: assert property (
        @(posedge CK) RST |=> (Q == 4'b0000)
    );

    // When not in reset, Q increments by one on the next clock.
    check_count_increments: assert property (
        @(posedge CK) disable iff (RST) 1'b1 |=> (Q == ($past(Q) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps: assert property (
        @(posedge CK) disable iff (RST) (Q == 4'hF) |=> (Q == 4'h0)
    );

endmodule