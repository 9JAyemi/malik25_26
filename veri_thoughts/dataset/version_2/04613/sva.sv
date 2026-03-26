module arithmetic_unit_sva(
    input logic        clk,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [1:0]  op,
    input logic [31:0] result
);

    // Result is always zero-extended in the upper 16 bits.
    check_result_upper_zero: assert property (
        @(posedge clk) result[31:16] == 16'd0
    );

    // op=2'b10 selects the bitwise AND result.
    check_and_select: assert property (
        @(posedge clk) (op == 2'b10) |-> (result == {16'd0, (a & b)})
    );

    // op=2'b01 selects the subtraction result.
    check_sub_select: assert property (
        @(posedge clk) (op == 2'b01) |-> (result == {16'd0, (a - b)})
    );

    // op=2'b00 selects the addition result.
    check_add_select_00: assert property (
        @(posedge clk) (op == 2'b00) |-> (result == {16'd0, (a + b)})
    );

    // op=2'b11 falls through to the addition result.
    check_add_select_11: assert property (
        @(posedge clk) (op == 2'b11) |-> (result == {16'd0, (a + b)})
    );

    // Result matches the implemented priority and mux logic.
    check_result_function: assert property (
        @(posedge clk)
        result == ((op == 2'b10) ? {16'd0, (a & b)} :
                   (op == 2'b01) ? {16'd0, (a - b)} :
                                   {16'd0, (a + b)})
    );

endmodule