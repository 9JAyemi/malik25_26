module add_sub_sva (
    input logic clk,
    input logic reset,
    input logic operation,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] result
);

    // Active-low reset forces the result to zero.
    check_reset_clears_result: assert property (
        @(posedge clk) !reset |-> (result == 4'b0000)
    );

    // In add mode, result captures A + B on the next clock.
    check_add_mode_result: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b0) |=> (result == ($past(A) + $past(B)))
    );

    // In subtract mode, result captures A - B on the next clock.
    check_sub_mode_result: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b1) |=> (result == ($past(A) - $past(B)))
    );

endmodule