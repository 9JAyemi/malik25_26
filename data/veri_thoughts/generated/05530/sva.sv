module up_down_counter_sva (
    input logic       up_down,
    input logic       load,
    input logic       clock,
    input logic       reset,
    input logic [3:0] count
);

    // Count is zero whenever the active-low reset is asserted.
    check_reset_clears_count: assert property (
        @(posedge clock) !reset |-> (count == 4'h0)
    );

    // A load sampled on the prior clock drives the count to zero.
    check_load_clears_count: assert property (
        @(posedge clock) disable iff (!reset)
        ($past(reset) && $past(load)) |-> (count == 4'h0)
    );

    // An up-count step that ends nonzero must be previous count plus one.
    check_count_up_nonzero_step: assert property (
        @(posedge clock) disable iff (!reset)
        ($past(reset) && !$past(load) && $past(up_down) && (count != 4'h0))
        |-> (count == ($past(count) + 4'h1))
    );

    // Counting up from 4'hF wraps to 4'h0.
    check_count_up_wrap_to_zero: assert property (
        @(posedge clock) disable iff (!reset)
        ($past(reset) && !$past(load) && $past(up_down) && ($past(count) == 4'hF))
        |-> (count == 4'h0)
    );

    // A down-count step that ends nonzero must be previous count minus one.
    check_count_down_nonzero_step: assert property (
        @(posedge clock) disable iff (!reset)
        ($past(reset) && !$past(load) && !$past(up_down) && (count != 4'h0))
        |-> (count == ($past(count) - 4'h1))
    );

    // Counting down from 4'h1 reaches 4'h0.
    check_count_down_to_zero: assert property (
        @(posedge clock) disable iff (!reset)
        ($past(reset) && !$past(load) && !$past(up_down) && ($past(count) == 4'h1))
        |-> (count == 4'h0)
    );

endmodule