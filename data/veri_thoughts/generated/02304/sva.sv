module basic_Calculator_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in1,
    input logic [7:0] data_in2,
    input logic [1:0] ctrl,
    input logic [7:0] result
);
    // Result is zero during synchronous reset.
    check_reset_clears_result: assert property (
        @(posedge clk) reset |-> (result == 8'h00)
    );

    // Add: next-cycle result equals LSB 8 bits of sum of current inputs.
    check_add_result: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b00) |=> (result == (($past(data_in1) + $past(data_in2))[7:0]))
    );

    // Sub: next-cycle result equals LSB 8 bits of difference of current inputs.
    check_sub_result: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b01) |=> (result == (($past(data_in1) - $past(data_in2))[7:0]))
    );

    // Mul: next-cycle result equals LSB 8 bits of product of current inputs.
    check_mul_result: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b10) |=> (result == (($past(data_in1) * $past(data_in2))[7:0]))
    );

    // Div: next-cycle result equals quotient when divisor != 0.
    check_div_result_no_by_zero: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b11 && (data_in2 != 8'h00)) |=> (result == ($past(data_in1) / $past(data_in2)))
    );

    // Add identity: adding zero on right returns left operand next cycle.
    check_add_identity_rhs_zero: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b00 && (data_in2 == 8'h00)) |=> (result == $past(data_in1))
    );

    // Add identity: adding zero on left returns right operand next cycle.
    check_add_identity_lhs_zero: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b00 && (data_in1 == 8'h00)) |=> (result == $past(data_in2))
    );

    // Sub identity: subtracting zero returns left operand next cycle.
    check_sub_identity_rhs_zero: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b01 && (data_in2 == 8'h00)) |=> (result == $past(data_in1))
    );

    // Sub zero: subtracting equal operands yields zero next cycle.
    check_sub_zero_when_equal: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b01 && (data_in1 == data_in2)) |=> (result == 8'h00)
    );

    // Mul by zero: any zero operand yields zero next cycle.
    check_mul_zero_operand_zero: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b10 && ((data_in1 == 8'h00) || (data_in2 == 8'h00))) |=> (result == 8'h00)
    );

    // Div identity: dividing by one returns numerator next cycle.
    check_div_identity_by_one: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b11 && (data_in2 == 8'h01)) |=> (result == $past(data_in1))
    );

    // Div zero numerator: zero divided by non-zero yields zero next cycle.
    check_div_zero_numerator: assert property (
        @(posedge clk) disable iff (reset)
            (ctrl == 2'b11 && (data_in1 == 8'h00) && (data_in2 != 8'h00)) |=> (result == 8'h00)
    );
endmodule