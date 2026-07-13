module up_down_counter_sva (
    input logic clk,
    input logic [3:0] D,
    input logic UD,
    input logic CE,
    input logic [3:0] Q
);

    // When enabled in up mode, Q increments on the next clock.
    check_increment_when_enabled_up: assert property (
        @(posedge clk)
        (CE && UD) |=> (Q == ($past(Q) + 4'd1))
    );

    // When enabled in down mode, Q decrements on the next clock.
    check_decrement_when_enabled_down: assert property (
        @(posedge clk)
        (CE && !UD) |=> (Q == ($past(Q) - 4'd1))
    );

    // When not enabled, Q loads D on the next clock.
    check_load_d_when_disabled: assert property (
        @(posedge clk)
        (!CE) |=> (Q == $past(D))
    );

    // Counting up from 4'hF wraps Q to 4'h0.
    check_up_wraparound: assert property (
        @(posedge clk)
        (CE && UD && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // Counting down from 4'h0 wraps Q to 4'hF.
    check_down_wraparound: assert property (
        @(posedge clk)
        (CE && !UD && (Q == 4'h0)) |=> (Q == 4'hF)
    );

    // Q always follows the RTL next-state function.
    check_complete_next_state: assert property (
        @(posedge clk)
        1'b1 |=> (Q == ($past(CE) ? ($past(UD) ? ($past(Q) + 4'd1) : ($past(Q) - 4'd1)) : $past(D)))
    );

endmodule