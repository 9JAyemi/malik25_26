module shift_register_sva (
    input logic       clk,
    input logic       d,
    input logic       q,
    input logic [2:0] buffer
);

    // q is always driven from the buffer MSB.
    check_q_matches_buffer_msb: assert property (
        @(posedge clk) q === buffer[2]
    );

    // The buffer LSB captures d on each rising clock edge.
    check_buffer_lsb_captures_d: assert property (
        @(posedge clk) 1'b1 |=> buffer[0] === $past(d)
    );

    // The middle buffer bit shifts in the previous LSB.
    check_buffer_mid_shifts_lsb: assert property (
        @(posedge clk) 1'b1 |=> buffer[1] === $past(buffer[0])
    );

    // The buffer MSB shifts in the previous middle bit.
    check_buffer_msb_shifts_mid: assert property (
        @(posedge clk) 1'b1 |=> buffer[2] === $past(buffer[1])
    );

    // The full buffer update matches the RTL concatenation.
    check_buffer_update_concatenation: assert property (
        @(posedge clk) 1'b1 |=> buffer === {$past(buffer[1:0]), $past(d)}
    );

    // q becomes the previous middle buffer bit after a clock.
    check_q_tracks_previous_mid_bit: assert property (
        @(posedge clk) 1'b1 |=> q === $past(buffer[1])
    );

    // After three clocks, q matches d delayed by three cycles.
    check_q_is_three_cycle_delayed_d: assert property (
        @(posedge clk)
        !($initstate || $past($initstate) || $past($initstate,2)) |-> q === $past(d,3)
    );

endmodule