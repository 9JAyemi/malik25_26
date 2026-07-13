module dynamic_gate_sva (
    input logic in,
    input logic clk,
    input logic out
);

// Next-cycle out equals previous-cycle in.
    check_out_follows_prev_in: assert property (
        @(posedge clk) 1'b1 |=> (out == $past(in))
    );

// If in was 1 on the previous cycle, out is 1 now.
    check_out_high_when_prev_in_high: assert property (
        @(posedge clk) $past(in) |-> (out == 1'b1)
    );

// If in was 0 on the previous cycle, out is 0 now.
    check_out_low_when_prev_in_low: assert property (
        @(posedge clk) !$past(in) |-> (out == 1'b0)
    );

// If out is 1 now, previous cycle's in was 1.
    check_prev_in_high_when_out_high: assert property (
        @(posedge clk) 1'b1 |=> (out == 1'b1) |-> $past(in) == 1'b1
    );

// If out is 0 now, previous cycle's in was 0.
    check_prev_in_low_when_out_low: assert property (
        @(posedge clk) 1'b1 |=> (out == 1'b0) |-> !$past(in)
    );

endmodule
