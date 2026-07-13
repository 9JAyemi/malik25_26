module up_down_counter_4bit_sva (
    input logic clk,
    input logic Up,
    input logic Down,
    input logic [3:0] Q
);

    // Up increments Q when not at 4'hF.
    check_up_increments: assert property (
        @(posedge clk) disable iff ($initstate)
        (Up && (Q != 4'hF)) |=> (Q == ($past(Q) + 4'd1))
    );

    // Up wraps Q from 4'hF to 4'h0.
    check_up_wraps: assert property (
        @(posedge clk) disable iff ($initstate)
        (Up && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // Down decrements Q when not at 4'h0.
    check_down_decrements: assert property (
        @(posedge clk) disable iff ($initstate)
        (!Up && Down && (Q != 4'h0)) |=> (Q == ($past(Q) - 4'd1))
    );

    // Down wraps Q from 4'h0 to 4'hF.
    check_down_wraps: assert property (
        @(posedge clk) disable iff ($initstate)
        (!Up && Down && (Q == 4'h0)) |=> (Q == 4'hF)
    );

    // With no control asserted, Q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff ($initstate)
        (!Up && !Down) |=> (Q == $past(Q))
    );

    // With both controls asserted, Up has priority over Down.
    check_up_priority_over_down: assert property (
        @(posedge clk) disable iff ($initstate)
        (Up && Down) |=> (Q == ($past(Q) + 4'd1))
    );

endmodule