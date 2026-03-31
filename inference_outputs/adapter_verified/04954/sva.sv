module pipelined_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT
);

// OUT reflects the 4-bit sum of A and B from two cycles earlier.
    check_out_two_cycle_latency: assert property (
        @(posedge clk) 1'b1 |-> ##2 OUT == ($past(A,2) + $past(B,2))
    );

// Zero on A passes B through two cycles later.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (A == 4'h0) |-> ##2 OUT == $past(B,2)
    );

// Zero on B passes A through two cycles later.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> ##2 OUT == $past(A,2)
    );

// Maximum 4-bit addition wraps from 15+15 to 0.
    check_max_sum_wraps: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF)) |-> ##2 OUT == 4'h0
    );

endmodule
