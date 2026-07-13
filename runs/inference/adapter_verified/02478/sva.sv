module sync_up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic [2:0] q
);

// Up mode: 7 wraps to 0.
    check_up_wrap_from_max: assert property (
        @(posedge clk) (up_down == 1'b0) && (q == 3'd7) |=> (q == 3'd0)
    );

// Up mode: 0..6 increment by 1.
    check_up_increment: assert property (
        @(posedge clk) (up_down == 1'b0) && (q != 3'd7) |=> (q == ($past(q) + 3'd1))
    );

// Down mode: 0 wraps to 7.
    check_down_wrap_from_zero: assert property (
        @(posedge clk) (up_down == 1'b1) && (q == 3'd0) |=> (q == 3'd7)
    );

// Down mode: 1..7 decrement by 1.
    check_down_decrement: assert property (
        @(posedge clk) (up_down == 1'b1) && (q != 3'd0) |=> (q == ($past(q) - 3'd1))
    );

endmodule
