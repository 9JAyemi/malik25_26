module max_val_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [15:0] max_val
);
    // max_val equals max($past(in), $past(max_val)) each cycle.
    check_next_equals_max_of_past: assert property (
        @(posedge clk)
            (!$isunknown($past(in)) && !$isunknown($past(max_val))) |->
            (max_val == (($past(in) > $past(max_val)) ? $past(in) : $past(max_val)))
    );

    // max_val never decreases.
    check_monotonic_non_decreasing: assert property (
        @(posedge clk)
            (!$isunknown($past(max_val))) |->
            (max_val >= $past(max_val))
    );

    // If $past(in) > $past(max_val), update to $past(in).
    check_update_when_prev_in_greater: assert property (
        @(posedge clk)
            (!$isunknown($past(in)) && !$isunknown($past(max_val)) && ($past(in) > $past(max_val))) |->
            (max_val == $past(in))
    );

    // If $past(in) <= $past(max_val), hold previous value.
    check_hold_when_prev_in_not_greater: assert property (
        @(posedge clk)
            (!$isunknown($past(in)) && !$isunknown($past(max_val)) && ($past(in) <= $past(max_val))) |->
            (max_val == $past(max_val))
    );

    // If $past(in) == $past(max_val), no change occurs.
    check_no_change_on_equal: assert property (
        @(posedge clk)
            (!$isunknown($past(in)) && !$isunknown($past(max_val)) && ($past(in) == $past(max_val))) |->
            (max_val == $past(max_val))
    );

    // If max_val changes, it must be due to $past(in) > $past(max_val) and equals $past(in).
    check_change_characterization: assert property (
        @(posedge clk)
            (!$isunknown($past(in)) && !$isunknown($past(max_val)) && !$isunknown(max_val) && (max_val != $past(max_val))) |->
            (($past(in) > $past(max_val)) && (max_val == $past(in)))
    );

    // Any change is a strict increase.
    check_strict_increase_on_change: assert property (
        @(posedge clk)
            (!$isunknown($past(max_val)) && !$isunknown(max_val) && (max_val != $past(max_val))) |->
            (max_val > $past(max_val))
    );

    // Current max_val is either $past(in) or $past(max_val).
    check_current_is_prev_in_or_prev_max: assert property (
        @(posedge clk)
            (!$isunknown($past(in)) && !$isunknown($past(max_val))) |->
            (max_val == $past(in) || max_val == $past(max_val))
    );
endmodule