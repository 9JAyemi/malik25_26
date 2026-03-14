module counter_sva (
    input logic clk,
    input logic [15:0] count
);
    // Next state equals prev+1, or wraps to 0 from 0xFFFF.
    check_update_rule: assert property (
        @(posedge clk) $past(1'b1) |-> (count == (($past(count) == 16'hFFFF) ? 16'h0000 : ($past(count) + 16'h0001)))
    );

    // Only 0xFFFF can be followed by 0x0000.
    check_zero_only_after_max: assert property (
        @(posedge clk) ($past(1'b1) && (count == 16'h0000)) |-> ($past(count) == 16'hFFFF)
    );

    // For nonzero count, previous value must be current - 1.
    check_prev_is_curr_minus1_when_nonzero: assert property (
        @(posedge clk) ($past(1'b1) && (count != 16'h0000)) |-> ($past(count) == (count - 16'h0001))
    );

    // Counter value must change every cycle.
    check_never_stable: assert property (
        @(posedge clk) $past(1'b1) |-> (count != $past(count))
    );
endmodule