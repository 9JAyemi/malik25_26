module up_counter_sva(
    input logic [3:0] Q,
    input logic       CLK,
    input logic       RST
);

    // When reset is low at a clock edge, the counter output is zero.
    check_reset_low_holds_zero: assert property (
        @(posedge CLK)
        !RST |-> (Q == 4'b0000)
    );

    // A falling reset clears the counter by the next sampled event.
    check_reset_fall_clears_q: assert property (
        @(posedge CLK or negedge RST)
        $fell(RST) |=> (Q == 4'b0000)
    );

    // The first active sample after reset still shows zero before counting.
    check_first_active_cycle_starts_from_zero: assert property (
        @(posedge CLK or negedge RST) disable iff (!RST)
        !$initstate && !$past(RST) |-> (Q == 4'b0000)
    );

    // On consecutive active samples, the counter increments by one modulo 16.
    check_counter_increments: assert property (
        @(posedge CLK or negedge RST) disable iff (!RST)
        !$initstate && $past(RST) |-> (Q == ($past(Q) + 4'd1))
    );

    // The counter wraps from 4'hF back to 4'h0.
    check_wrap_from_f_to_0: assert property (
        @(posedge CLK or negedge RST) disable iff (!RST)
        !$initstate && $past(RST) && ($past(Q) == 4'hF) |-> (Q == 4'h0)
    );

endmodule