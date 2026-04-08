module counter_sva #(parameter WIDTH = 8) (
    input logic rstn,
    input logic clk,
    input logic up,
    input logic down,
    input logic [WIDTH-1:0] count
);

    // Active-low reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rstn |-> (count == {WIDTH{1'b0}})
    );

    // up without down increments count by one.
    check_increment_when_up_only: assert property (
        @(posedge clk) disable iff (!rstn)
        (up && !down) |=> (count == ($past(count) + 1'b1))
    );

    // down without up decrements count by one.
    check_decrement_when_down_only: assert property (
        @(posedge clk) disable iff (!rstn)
        (!up && down) |=> (count == ($past(count) - 1'b1))
    );

    // With neither input asserted, count holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (!rstn)
        (!up && !down) |=> (count == $past(count))
    );

    // With both inputs asserted, count holds its value.
    check_hold_when_up_and_down: assert property (
        @(posedge clk) disable iff (!rstn)
        (up && down) |=> (count == $past(count))
    );

endmodule