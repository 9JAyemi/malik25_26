module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Reset forces count to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 4'b0000)
    );

    // With enable low and count at 0, the next count stays 0.
    check_zero_state_clears: assert property (
        @(posedge clk) disable iff (reset)
        (!enable && (count == 4'b0000)) |=> (count == 4'b0000)
    );

    // With enable low and count at 1, the next count increments to 2.
    check_one_state_increments: assert property (
        @(posedge clk) disable iff (reset)
        (!enable && (count == 4'b0001)) |=> (count == 4'b0010)
    );

    // With enable low and count at 9, the next count clears to 0.
    check_nine_state_clears: assert property (
        @(posedge clk) disable iff (reset)
        (!enable && (count == 4'b1001)) |=> (count == 4'b0000)
    );

    // With enable high, count holds its value.
    check_enable_high_holds: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> $stable(count)
    );

    // With enable low and unmatched counts, count holds its value.
    check_unmatched_cases_hold: assert property (
        @(posedge clk) disable iff (reset)
        (!enable && (count != 4'b0000) && (count != 4'b0001) && (count != 4'b1001)) |=> $stable(count)
    );

endmodule