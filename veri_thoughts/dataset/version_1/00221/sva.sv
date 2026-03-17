module binary_counter_assertions (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count_out
);

    // While active-low reset is asserted, the counter output is zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        !reset |-> (count_out == 4'h0)
    );

    // On the first sampled clock after reset is released, the counter is one.
    check_release_from_reset_starts_at_one: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        $rose(reset) |-> (count_out == 4'h1)
    );

    // A sampled zero is followed by one on the next active clock.
    check_zero_advances_to_one: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        ($past(count_out) == 4'h0) |-> (count_out == 4'h1)
    );

    // Any active count value other than one must equal the previous value plus one.
    check_active_counts_increment_except_one: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        (count_out != 4'h1) |-> (count_out == ($past(count_out) + 4'd1))
    );

    // A zero during active counting can only occur after the maximum count.
    check_wrap_to_zero_from_fifteen: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        (count_out == 4'h0) |-> ($past(count_out) == 4'hF)
    );

endmodule