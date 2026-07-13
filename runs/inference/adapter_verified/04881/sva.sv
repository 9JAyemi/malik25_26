module up_down_counter_4bit_sva (
    input logic clk,
    input logic Up,
    input logic Down,
    input logic [3:0] Q
);

// Up increments Q when not at max; else holds.
    check_up_increments_or_holds: assert property (
        @(posedge clk) Up |-> ((Q == 4'hF) ? (Q == 4'hF) : (Q == ($past(Q) + 4'd1)))
    );

// Down decrements Q when not at zero; else holds.
    check_down_decrements_or_holds: assert property (
        @(posedge clk) Down |-> ((Q == 4'h0) ? (Q == 4'h0) : (Q == ($past(Q) - 4'd1)))
    );

// When both Up and Down are high, Up has priority and Q increments.
    check_priority_up_over_down: assert property (
        @(posedge clk) (Up && Down) |-> ((Q == 4'hF) ? (Q == 4'hF) : (Q == ($past(Q) + 4'd1)))
    );

// When both Up and Down are high, Down has no effect.
    check_priority_up_over_down_no_change: assert property (
        @(posedge clk) (Up && Down) |-> (Q == $past(Q))
    );

// If neither control is high, Q holds.
    check_hold_when_idle: assert property (
        @(posedge clk) (!Up && !Down) |-> (Q == $past(Q))
    );

// If Q is 0 and Down is high, Q wraps to 15.
    check_wrap_down_from_zero: assert property (
        @(posedge clk) (Down && (Q == 4'h0)) |-> (Q == 4'hF)
    );

// If Q is 15 and Up is high, Q wraps to 0.
    check_wrap_up_from_max: assert property (
        @(posedge clk) (Up && (Q == 4'hF)) |-> (Q == 4'h0)
    );

endmodule
