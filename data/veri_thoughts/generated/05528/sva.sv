module add_sub_4bit_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       mode,
    input logic       clk,
    input logic [3:0] result
);

    // In addition mode, result captures the prior cycle sum.
    check_addition_mode: assert property (
        @(posedge clk) (mode == 1'b1) |=> (result == ($past(a) + $past(b)))
    );

    // In subtraction mode, result captures the prior cycle difference.
    check_subtraction_mode: assert property (
        @(posedge clk) (mode == 1'b0) |=> (result == ($past(a) - $past(b)))
    );

    // Result always matches the prior cycle operation selected by mode.
    check_selected_operation: assert property (
        @(posedge clk) 1'b1 |=> (result == ($past(mode) ? ($past(a) + $past(b)) : ($past(a) - $past(b))))
    );

    // Adding zero passes a through on the next cycle.
    check_add_zero_identity: assert property (
        @(posedge clk) ((mode == 1'b1) && (b == 4'b0000)) |=> (result == $past(a))
    );

    // Subtracting zero passes a through on the next cycle.
    check_sub_zero_identity: assert property (
        @(posedge clk) ((mode == 1'b0) && (b == 4'b0000)) |=> (result == $past(a))
    );

    // Subtracting equal operands yields zero on the next cycle.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) ((mode == 1'b0) && (a == b)) |=> (result == 4'b0000)
    );

endmodule