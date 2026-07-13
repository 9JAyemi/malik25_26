module binary_counter_sva (
    input logic CLK,
    input logic RST,
    input logic [3:0] Q
);
    ///// Reset behavior /////
    // When RST is asserted, Q must be 0 on the next clock.
    reset_forces_zero_next: assert property (
        @(posedge CLK) RST |=> (Q == 4'h0)
    );

    ///// Counting behavior (disabled during reset) /////
    // When not at max, Q increments by 1 on the next clock.
    count_increments_when_not_max: assert property (
        @(posedge CLK) disable iff (RST) (Q != 4'hF) |=> (Q == $past(Q) + 1'b1)
    );

    // When at max, Q wraps to 0 on the next clock.
    count_wraps_when_max: assert property (
        @(posedge CLK) disable iff (RST) (Q == 4'hF) |=> (Q == 4'h0)
    );

    // LSB toggles every cycle when not in reset.
    lsb_toggles_without_reset: assert property (
        @(posedge CLK) disable iff (RST) 1'b1 |=> (Q[0] == ~$past(Q[0]))
    );
endmodule