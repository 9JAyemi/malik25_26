module adder_subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Sub,
    input logic clk,
    input logic [3:0] result
);

    // In add mode, result captures A + B on the next clock.
    check_add_mode_result: assert property (
        @(posedge clk) (Sub == 1'b0) |=> (result == ($past(A) + $past(B)))
    );

    // In subtract mode, result captures A - B on the next clock.
    check_sub_mode_result: assert property (
        @(posedge clk) (Sub == 1'b1) |=> (result == ($past(A) - $past(B)))
    );

    // Result always reflects the operation selected on the previous clock.
    check_selected_operation_result: assert property (
        @(posedge clk) 1'b1 |=> (result == ($past(Sub) ? ($past(A) - $past(B)) : ($past(A) + $past(B))))
    );

    // Subtracting equal operands produces zero on the next clock.
    check_equal_operands_subtract_zero: assert property (
        @(posedge clk) (Sub == 1'b1 && A == B) |=> (result == 4'b0000)
    );

    // Adding zero on B passes A through on the next clock.
    check_add_zero_passthrough: assert property (
        @(posedge clk) (Sub == 1'b0 && B == 4'b0000) |=> (result == $past(A))
    );

endmodule