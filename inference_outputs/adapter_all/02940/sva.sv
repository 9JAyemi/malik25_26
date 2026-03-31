module add_sub_sva (
    input logic clk,
    input logic reset,
    input logic operation,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] result
);

    // Reset forces the registered result to zero.
    check_reset_clears_result: assert property (
        @(posedge clk) !reset |-> (result == 4'b0000)
    );

    // In add mode, the next result is the previous cycle's A+B.
    check_add_mode_updates_result: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b0) |=> (result == (($past(A) + $past(B)) & 4'hF))
    );

    // In subtract mode, the next result is the previous cycle's A-B.
    check_sub_mode_updates_result: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b1) |=> (result == (($past(A) - $past(B)) & 4'hF))
    );

    // With stable inputs and operation, the result holds its value.
    check_result_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (!reset)
        ($stable(operation) && $stable(A) && $stable(B)) |=> (result == $past(result))
    );

endmodule