module RCB_FRL_COUNT_TO_64_sva (
    input logic clk,
    input logic rst,
    input logic count,
    input logic ud,
    input logic [5:0] counter_value
);

    ///// Reset behavior /////
    // While reset is asserted, counter_value must be 0.
    reset_value_during_rst: assert property (
        @(posedge clk) rst |-> (counter_value == 6'h00)
    );

    ///// Count control /////
    // When count=0, hold previous value (ud is don't care).
    hold_when_count_low: assert property (
        @(posedge clk) disable iff (rst)
            (count == 1'b0 && $past(!rst)) |-> (counter_value == $past(counter_value))
    );

    // When count=1 and ud=1, increment by 1.
    increment_when_count_and_ud_high: assert property (
        @(posedge clk) disable iff (rst)
            (count && ud && $past(!rst)) |-> (counter_value == ($past(counter_value) + 6'd1))
    );

    // When count=1 and ud=0, decrement by 1.
    decrement_when_count_high_ud_low: assert property (
        @(posedge clk) disable iff (rst)
            (count && !ud && $past(!rst)) |-> (counter_value == ($past(counter_value) - 6'd1))
    );

    ///// Wrap-around behavior /////
    // Increment from 6'h3F wraps to 6'h00.
    wrap_to_zero_when_incrementing_from_max: assert property (
        @(posedge clk) disable iff (rst)
            (count && ud && $past(!rst) && ($past(counter_value) == 6'h3F)) |-> (counter_value == 6'h00)
    );

    // Decrement from 6'h00 wraps to 6'h3F.
    wrap_to_max_when_decrementing_from_zero: assert property (
        @(posedge clk) disable iff (rst)
            (count && !ud && $past(!rst) && ($past(counter_value) == 6'h00)) |-> (counter_value == 6'h3F)
    );

    ///// Change characterization /////
    // When count=1, the value must change (either +1 or -1).
    change_occurs_when_count_high: assert property (
        @(posedge clk) disable iff (rst)
            (count && $past(!rst)) |-> (counter_value != $past(counter_value))
    );

    ///// Multi-cycle consistency /////
    // Two consecutive cycles of (count=1, ud=1) net +2 over two cycles.
    two_cycle_double_increment: assert property (
        @(posedge clk) disable iff (rst)
            (count && ud && $past(count) && $past(ud) && $past(!rst) && $past(!rst,2)) |-> 
            (counter_value == ($past(counter_value,2) + 6'd2))
    );

    // Two consecutive cycles of (count=1, ud=0) net -2 over two cycles.
    two_cycle_double_decrement: assert property (
        @(posedge clk) disable iff (rst)
            (count && !ud && $past(count) && !$past(ud) && $past(!rst) && $past(!rst,2)) |-> 
            (counter_value == ($past(counter_value,2) - 6'd2))
    );

    // With count=1 for two cycles and ud toggling, net change over two cycles is zero.
    two_cycle_ud_toggle_nets_zero: assert property (
        @(posedge clk) disable iff (rst)
            (count && $past(count) && (ud ^ $past(ud)) && $past(!rst) && $past(!rst,2)) |-> 
            (counter_value == $past(counter_value,2))
    );

endmodule