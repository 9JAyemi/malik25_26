module counter_4bit_assertions (
    input logic       clk,
    input logic       set_l,
    input logic [3:0] count
);

    // Active-low reset forces the count output to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) !set_l |-> (count == 4'h0)
    );

    // The first sampled active cycle after reset still shows zero.
    check_first_cycle_after_reset_zero: assert property (
        @(posedge clk) disable iff (!set_l)
        (!$initstate && !$past(set_l)) |-> (count == 4'h0)
    );

    // On consecutive sampled active cycles, count either increments or reflects an async reset pulse.
    check_active_cycle_progression: assert property (
        @(posedge clk) disable iff (!set_l)
        (!$initstate && $past(set_l)) |-> ((count == 4'h0) || (count == (($past(count) + 4'h1) & 4'hF)))
    );

    // A sampled value of 15 wraps to 0 on the next sampled active cycle.
    check_wrap_from_f_to_zero: assert property (
        @(posedge clk) disable iff (!set_l)
        (!$initstate && $past(set_l) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule