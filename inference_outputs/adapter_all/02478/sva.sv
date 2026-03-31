module sync_up_down_counter_sva (
    input logic clk,
    input logic up_down,
    input logic [2:0] q
);

    // Up mode increments from 0 to 7.
    check_up_mode_increment: assert property (
        @(posedge clk) (up_down == 1'b0 && q == 3'd0) |=> (q == 3'd1)
    );

    // Up mode increments from 1 to 7.
    check_up_mode_increment_mid: assert property (
        @(posedge clk) (up_down == 1'b0 && q == 3'd1) |=> (q == 3'd2)
    );

    // Up mode wraps from 7 back to 0.
    check_up_mode_wrap: assert property (
        @(posedge clk) (up_down == 1'b0 && q == 3'd7) |=> (q == 3'd0)
    );

    // Down mode decrements from 7 to 0.
    check_down_mode_decrement: assert property (
        @(posedge clk) (up_down == 1'b1 && q == 3'd7) |=> (q == 3'd6)
    );

    // Down mode decrements from 1 to 0.
    check_down_mode_decrement_mid: assert property (
        @(posedge clk) (up_down == 1'b1 && q == 3'd1) |=> (q == 3'd0)
    );

    // Down mode wraps from 0 back to 7.
    check_down_mode_wrap: assert property (
        @(posedge clk) (up_down == 1'b1 && q == 3'd0) |=> (q == 3'd7)
    );

endmodule