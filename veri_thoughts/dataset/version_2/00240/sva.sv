module sequential_circuit_sva (
    input logic       clk,
    input logic       a,
    input logic       b,
    input logic [1:0] q,
    input logic [1:0] counter,
    input logic       flip_flop
);

    // q is a direct reflection of the counter register.
    check_q_matches_counter: assert property (
        @(posedge clk) disable iff ($initstate)
        (q == counter)
    );

    // When only b was high, the counter resets to zero on the next cycle.
    check_counter_resets_on_b: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(b) && !$past(a)) |-> (counter == 2'b00)
    );

    // When both a and b were high, b has priority and the counter resets.
    check_b_priority_over_a: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(b) && $past(a)) |-> (counter == 2'b00)
    );

    // When only a was high, the counter increments by one on the next cycle.
    check_counter_increments_on_a: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(b) && $past(a)) |-> (counter == ($past(counter) + 2'b01))
    );

    // When neither input was high, the counter holds its value.
    check_counter_holds_when_idle: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(b) && !$past(a)) |-> (counter == $past(counter))
    );

    // flip_flop captures the previous cycle's counter MSB.
    check_flip_flop_tracks_counter_msb: assert property (
        @(posedge clk) disable iff ($initstate)
        (flip_flop == $past(counter[1]))
    );

endmodule