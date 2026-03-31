module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] signed_mag,
    input logic select,
    input logic [7:0] q
);

    // Reset clears the output on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (q == 8'h00)
    );

    // With select high, the output is the previous counter value zero-extended.
    check_select_high_uses_counter: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (q == {4'b0000, $past(q[3:0])})
    );

    // With select low, the output is the previous signed magnitude value zero-extended.
    check_select_low_uses_signed_mag: assert property (
        @(posedge clk) disable iff (reset)
        !select |=> (q == {4'b0000, $past(signed_mag)})
    );

    // The upper nibble is always zero after reset is released.
    check_output_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (q[7:4] == 4'b0000)
    );

    // The lower nibble follows the selected source from the previous cycle.
    check_output_lower_nibble_selected_source: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (q[3:0] == ($past(select) ? $past(q[3:0]) : $past(signed_mag)))
    );

endmodule