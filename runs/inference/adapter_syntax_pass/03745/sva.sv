module counter_4bit_sync_reset_sva (
    input logic       CK,
    input logic       RST,
    input logic [3:0] Q
);

    // Reset forces Q to zero on the next clock.
    check_reset_clears_q: assert property (
        @(posedge CK) RST |=> (Q == 4'h0)
    );

    // When not in reset, Q increments by one each clock.
    check_increment_when_not_reset: assert property (
        @(posedge CK) disable iff (RST) 1'b1 |=> (Q == ($past(Q) + 4'd1))
    );

    // The counter wraps from 15 back to 0.
    check_wrap_from_max: assert property (
        @(posedge CK) disable iff (RST) (Q == 4'hF) |=> (Q == 4'h0)
    );

endmodule