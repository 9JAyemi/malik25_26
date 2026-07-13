module up_down_counter_4bit_sva (
    input logic clk,
    input logic Up,
    input logic Down,
    input logic [3:0] Q
);

    // Up increments Q by one when Q is not at 15.
    check_up_increments: assert property (
        @(posedge clk) Up && (Q != 4'hF) |=> (Q == ($past(Q) + 4'd1))
    );

    // Up wraps Q from 15 back to 0.
    check_up_wraps: assert property (
        @(posedge clk) Up && (Q == 4'hF) |=> (Q == 4'h0)
    );

    // Down decrements Q by one when Q is not at 0.
    check_down_decrements: assert property (
        @(posedge clk) Down && !Up && (Q != 4'h0) |=> (Q == ($past(Q) - 4'd1))
    );

    // Down wraps Q from 0 back to 15.
    check_down_wraps: assert property (
        @(posedge clk) Down && !Up && (Q == 4'h0) |=> (Q == 4'hF)
    );

    // Q holds its value when neither control is asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) (!Up && !Down) |=> (Q == $past(Q))
    );

    // Up has priority over Down when both are asserted.
    check_up_priority_over_down: assert property (
        @(posedge clk) Up && Down |=> (Q == ($past(Q) + 4'd1))
    );

endmodule