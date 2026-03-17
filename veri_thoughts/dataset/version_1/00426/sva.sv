module adder_sva(
    input logic signed [15:0] a,
    input logic signed [15:0] b,
    input logic clk,
    input logic rst,
    input logic signed [15:0] sum
);

    // Sum matches the operation taken on the previous clock edge.
    check_sum_matches_previous_cycle_operation: assert property (
        @(posedge clk)
        1'b1 |=> (sum == ($past(rst) ? 16'sd0 : ($past(a) + $past(b))))
    );

    // A reset cycle drives sum to zero.
    check_reset_clears_sum: assert property (
        @(posedge clk)
        rst |=> (sum == 16'sd0)
    );

    // A non-reset cycle loads the previous sum of a and b.
    check_sum_updates_after_nonreset_cycle: assert property (
        @(posedge clk) disable iff (rst)
        !rst |=> (sum == ($past(a) + $past(b)))
    );

    // With a equal to zero, sum passes through the previous value of b.
    check_zero_a_passes_b: assert property (
        @(posedge clk) disable iff (rst)
        (!rst && (a == 16'sd0)) |=> (sum == $past(b))
    );

    // With b equal to zero, sum passes through the previous value of a.
    check_zero_b_passes_a: assert property (
        @(posedge clk) disable iff (rst)
        (!rst && (b == 16'sd0)) |=> (sum == $past(a))
    );

endmodule