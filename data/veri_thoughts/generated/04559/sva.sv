module multiplier_32bit_sva (
    input logic        clk,
    input logic [15:0] a_1,
    input logic [15:0] b_1,
    input logic [15:0] a_2,
    input logic [15:0] b_2,
    input logic        select,
    input logic [31:0] result,
    input logic [31:0] mul_result_1,
    input logic [31:0] mul_result_2
);

    // mult_1 output matches a_1 multiplied by b_1.
    check_mul1_product: assert property (
        @(posedge clk) 1'b1 |=> (mul_result_1 == (a_1 * b_1))
    );

    // mult_2 output matches a_2 multiplied by b_2.
    check_mul2_product: assert property (
        @(posedge clk) 1'b1 |=> (mul_result_2 == (a_2 * b_2))
    );

    // Data input changes alone do not update result when select is unchanged.
    check_result_ignores_data_only_changes: assert property (
        @(posedge clk) ($stable(select) && $changed({a_1, b_1, a_2, b_2})) |-> $stable(result)
    );

    // A falling select chooses multiplier 1 when its inputs are unchanged.
    check_select_low_loads_mul1: assert property (
        @(posedge clk) $fell(select) && $stable(a_1) && $stable(b_1) |-> (result == mul_result_1)
    );

    // A rising select chooses multiplier 2 when its inputs are unchanged.
    check_select_high_loads_mul2: assert property (
        @(posedge clk) $rose(select) && $stable(a_2) && $stable(b_2) |-> (result == mul_result_2)
    );

endmodule