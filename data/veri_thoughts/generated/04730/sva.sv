module addsub_assertions (
    input logic clk,
    input logic rst,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic sub,
    input logic [3:0] result
);
    // Clock: posedge clk
    // Reset: synchronous active-high rst
    // Logic: sequential registered add/sub selected by sub

    // After a reset cycle, result is cleared to zero.
    check_reset_clears_result: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (result == 4'b0000)
    );

    // In add mode, result matches the prior cycle sum.
    check_add_result: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) && !$past(sub) |-> (result == ($past(a) + $past(b)))
    );

    // In subtract mode, result matches the prior cycle difference.
    check_sub_result: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        !$past(rst) && $past(sub) |-> (result == ($past(a) - $past(b)))
    );

endmodule