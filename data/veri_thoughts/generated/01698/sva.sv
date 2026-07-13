module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic [1:0] count
);

    ///// Reset behavior /////
    // While reset is LOW at a clock edge, count must be 0.
    check_reset_clears_count: assert property (
        @(posedge clk) !reset |-> (count == 2'b00)
    );

    // On the first clock edge after reset rises, count becomes 1.
    check_first_count_after_reset_release: assert property (
        @(posedge clk) disable iff (!reset)
            (reset && !$past(reset)) |-> (count == 2'b01)
    );

    ///// Counting behavior (when reset is HIGH on consecutive cycles) /////
    // Allowed transitions: 00->01, 01->10, 10->11, 11->00.
    check_allowed_transitions: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && reset) |-> (
                (($past(count) == 2'b00) && (count == 2'b01)) ||
                (($past(count) == 2'b01) && (count == 2'b10)) ||
                (($past(count) == 2'b10) && (count == 2'b11)) ||
                (($past(count) == 2'b11) && (count == 2'b00))
            )
    );

    // LSB toggles every cycle when reset is HIGH on consecutive cycles.
    check_lsb_toggles: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && reset) |-> (count[0] != $past(count[0]))
    );

    // MSB toggles when previous count was 01 or 11.
    check_msb_toggles_on_1_or_3: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && reset && ($past(count) inside {2'b01, 2'b11})) |-> (count[1] != $past(count[1]))
    );

    // MSB holds when previous count was 00 or 10.
    check_msb_holds_on_0_or_2: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && reset && ($past(count) inside {2'b00, 2'b10})) |-> (count[1] == $past(count[1]))
    );

    // Count changes every cycle when reset is HIGH on consecutive cycles.
    check_count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && reset) |-> (count != $past(count))
    );

    // Modulo-4 periodicity: after 4 cycles with reset HIGH, count repeats.
    check_modulo4_periodicity: assert property (
        @(posedge clk) disable iff (!reset)
            (reset && $past(reset,1) && $past(reset,2) && $past(reset,3) && $past(reset,4)) |-> (count == $past(count,4))
    );

endmodule