module calculator_sva (
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [1:0] op,
    input logic [7:0] result
);
    // No clock/reset in RTL; combinational; sample on any input edge.

    // When op==00, result equals 8-bit sum of num1 and num2.
    check_add_result: assert property (
        @(posedge num1[0] or negedge num1[0] or
          posedge num1[1] or negedge num1[1] or
          posedge num1[2] or negedge num1[2] or
          posedge num1[3] or negedge num1[3] or
          posedge num1[4] or negedge num1[4] or
          posedge num1[5] or negedge num1[5] or
          posedge num1[6] or negedge num1[6] or
          posedge num1[7] or negedge num1[7] or
          posedge num2[0] or negedge num2[0] or
          posedge num2[1] or negedge num2[1] or
          posedge num2[2] or negedge num2[2] or
          posedge num2[3] or negedge num2[3] or
          posedge num2[4] or negedge num2[4] or
          posedge num2[5] or negedge num2[5] or
          posedge num2[6] or negedge num2[6] or
          posedge num2[7] or negedge num2[7] or
          posedge op[0] or negedge op[0] or
          posedge op[1] or negedge op[1])
        (op == 2'b00) |-> (result == (num1 + num2))
    );

    // When op==01, result equals 8-bit difference num1 - num2.
    check_sub_result: assert property (
        @(posedge num1[0] or negedge num1[0] or
          posedge num1[1] or negedge num1[1] or
          posedge num1[2] or negedge num1[2] or
          posedge num1[3] or negedge num1[3] or
          posedge num1[4] or negedge num1[4] or
          posedge num1[5] or negedge num1[5] or
          posedge num1[6] or negedge num1[6] or
          posedge num1[7] or negedge num1[7] or
          posedge num2[0] or negedge num2[0] or
          posedge num2[1] or negedge num2[1] or
          posedge num2[2] or negedge num2[2] or
          posedge num2[3] or negedge num2[3] or
          posedge num2[4] or negedge num2[4] or
          posedge num2[5] or negedge num2[5] or
          posedge num2[6] or negedge num2[6] or
          posedge num2[7] or negedge num2[7] or
          posedge op[0] or negedge op[0] or
          posedge op[1] or negedge op[1])
        (op == 2'b01) |-> (result == (num1 - num2))
    );

    // When op==10, result equals low 8 bits of num1 * num2.
    check_mul_result: assert property (
        @(posedge num1[0] or negedge num1[0] or
          posedge num1[1] or negedge num1[1] or
          posedge num1[2] or negedge num1[2] or
          posedge num1[3] or negedge num1[3] or
          posedge num1[4] or negedge num1[4] or
          posedge num1[5] or negedge num1[5] or
          posedge num1[6] or negedge num1[6] or
          posedge num1[7] or negedge num1[7] or
          posedge num2[0] or negedge num2[0] or
          posedge num2[1] or negedge num2[1] or
          posedge num2[2] or negedge num2[2] or
          posedge num2[3] or negedge num2[3] or
          posedge num2[4] or negedge num2[4] or
          posedge num2[5] or negedge num2[5] or
          posedge num2[6] or negedge num2[6] or
          posedge num2[7] or negedge num2[7] or
          posedge op[0] or negedge op[0] or
          posedge op[1] or negedge op[1])
        (op == 2'b10) |-> (result == (num1 * num2)[7:0])
    );

    // When op==11 and num2!=0, result equals num1 / num2.
    check_div_result: assert property (
        @(posedge num1[0] or negedge num1[0] or
          posedge num1[1] or negedge num1[1] or
          posedge num1[2] or negedge num1[2] or
          posedge num1[3] or negedge num1[3] or
          posedge num1[4] or negedge num1[4] or
          posedge num1[5] or negedge num1[5] or
          posedge num1[6] or negedge num1[6] or
          posedge num1[7] or negedge num1[7] or
          posedge num2[0] or negedge num2[0] or
          posedge num2[1] or negedge num2[1] or
          posedge num2[2] or negedge num2[2] or
          posedge num2[3] or negedge num2[3] or
          posedge num2[4] or negedge num2[4] or
          posedge num2[5] or negedge num2[5] or
          posedge num2[6] or negedge num2[6] or
          posedge num2[7] or negedge num2[7] or
          posedge op[0] or negedge op[0] or
          posedge op[1] or negedge op[1])
        (op == 2'b11 && num2 != 8'd0) |-> (result == (num1 / num2))
    );

    // For division by 1, result equals num1.
    check_div_by_one: assert property (
        @(posedge num1[0] or negedge num1[0] or
          posedge num1[1] or negedge num1[1] or
          posedge num1[2] or negedge num1[2] or
          posedge num1[3] or negedge num1[3] or
          posedge num1[4] or negedge num1[4] or
          posedge num1[5] or negedge num1[5] or
          posedge num1[6] or negedge num1[6] or
          posedge num1[7] or negedge num1[7] or
          posedge num2[0] or negedge num2[0] or
          posedge num2[1] or negedge num2[1] or
          posedge num2[2] or negedge num2[2] or
          posedge num2[3] or negedge num2[3] or
          posedge num2[4] or negedge num2[4] or
          posedge num2[5] or negedge num2[5] or
          posedge num2[6] or negedge num2[6] or
          posedge num2[7] or negedge num2[7] or
          posedge op[0] or negedge op[0] or
          posedge op[1] or negedge op[1])
        (op == 2'b11 && num2 == 8'd1) |-> (result == num1)
    );

    // For division by 2, result equals num1/2 (truncating).
    check_div_by_two: assert property (
        @(posedge num1[0] or negedge num1[0] or
          posedge num1[1] or negedge num1[1] or
          posedge num1[2] or negedge num1[2] or
          posedge num1[3] or negedge num1[3] or
          posedge num1[4] or negedge num1[