module tracking_camera_system_altpll_0_dffpipe_l2c_sva (
    input logic clock,
    input logic [0:0] d,
    input logic [0:0] q
);

    // q matches d delayed by three clocks.
    check_q_three_cycle_delay: assert property (
        @(posedge clock) disable iff (1'b0)
        (!($initstate || $past($initstate) || $past($initstate,2) || $past($initstate,3)))
        |-> (q[0] === $past(d[0],3))
    );

    // A high input reaches q after three clocks.
    check_high_propagates_to_q: assert property (
        @(posedge clock) disable iff (1'b0)
        d[0] |-> ##3 q[0]
    );

    // A low input reaches q after three clocks.
    check_low_propagates_to_q: assert property (
        @(posedge clock) disable iff (1'b0)
        !d[0] |-> ##3 !q[0]
    );

    // A rising edge on d appears on q three clocks later.
    check_rise_propagates_to_q: assert property (
        @(posedge clock) disable iff (1'b0)
        ((!$initstate) && $rose(d[0])) |-> ##3 $rose(q[0])
    );

    // A falling edge on d appears on q three clocks later.
    check_fall_propagates_to_q: assert property (
        @(posedge clock) disable iff (1'b0)
        ((!$initstate) && $fell(d[0])) |-> ##3 $fell(q[0])
    );

    // One-cycle input stability is preserved at q three clocks later.
    check_stable_input_gives_stable_output: assert property (
        @(posedge clock) disable iff (1'b0)
        (d[0] === $past(d[0])) |-> ##3 (q[0] === $past(q[0]))
    );

endmodule