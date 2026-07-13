module top_module_sva (
    input logic clk,
    input logic reset, // synchronous active-high
    input logic up_down,
    input logic enable,
    input logic [7:0] q,
    input logic [1:0] counter_out,
    input logic [1:0] gray_out
);

    // Reset clears the counter on the next clock.
    check_counter_clears_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (counter_out == 2'b00)
    );

    // Reset clears the Gray output on the next clock.
    check_gray_clears_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (gray_out == 2'b00)
    );

    // Reset clears the top-level output on the next clock.
    check_q_clears_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (q == 8'h00)
    );

    // With enable low, the counter holds its value.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (counter_out == $past(counter_out))
    );

    // With enable high and up_down high, the counter increments by one.
    check_counter_increments_when_up: assert property (
        @(posedge clk) disable iff (reset)
        enable && up_down |=> (counter_out == ($past(counter_out) + 2'b01))
    );

    // With enable high and up_down low, the counter decrements by one.
    check_counter_decrements_when_down: assert property (
        @(posedge clk) disable iff (reset)
        enable && !up_down |=> (counter_out == ($past(counter_out) - 2'b01))
    );

    // Gray code 00 maps to 00.
    check_gray_decode_00: assert property (
        @(posedge clk) disable iff (reset)
        (gray_out == 2'b00) |-> (counter_out == 2'b00)
    );

    // Gray code 01 maps to 01.
    check_gray_decode_01: assert property (
        @(posedge clk) disable iff (reset)
        (gray_out == 2'b01) |-> (counter_out == 2'b01)
    );

    // Gray code 11 maps to 11.
    check_gray_decode_11: assert property (
        @(posedge clk) disable iff (reset)
        (gray_out == 2'b11) |-> (counter_out == 2'b11)
    );

    // Gray code 10 maps to 10.
    check_gray_decode_10: assert property (
        @(posedge clk) disable iff (reset)
        (gray_out == 2'b10) |-> (counter_out == 2'b10)
    );

    // The top-level output is always {gray_out, counter_out}.
    check_q_matches_concatenation: assert property (
        @(posedge clk) disable iff (reset)
        (q == {gray_out, counter_out})
    );

endmodule