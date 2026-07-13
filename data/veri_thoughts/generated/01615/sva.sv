module calculator_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] op,
    input logic [3:0] result
);
    // For op==00, result is low 4 bits of a+b.
    check_addition_result: assert property (
        @(posedge a[0] or posedge b[0] or posedge op[0] or posedge op[1]) (op == 2'b00) |-> (result == (a + b)[3:0])
    );

    // For op==01, result is low 4 bits of a-b.
    check_subtraction_result: assert property (
        @(posedge a[0] or posedge b[0] or posedge op[0] or posedge op[1]) (op == 2'b01) |-> (result == (a - b)[3:0])
    );

    // For op values not 00/01 (i.e., 10 or 11), result is 0.
    check_default_zero_for_other_ops: assert property (
        @(posedge a[0] or posedge b[0] or posedge op[0] or posedge op[1]) (op[1] == 1'b1) |-> (result == 4'b0000)
    );

    // Addition identity: when op==00 and b==0, result equals a.
    check_addition_with_b_zero: assert property (
        @(posedge a[0] or posedge b[0] or posedge op[0] or posedge op[1]) ((op == 2'b00) && (b == 4'b0000)) |-> (result == a)
    );

    // Addition identity: when op==00 and a==0, result equals b.
    check_addition_with_a_zero: assert property (
        @(posedge a[0] or posedge b[0] or posedge op[0] or posedge op[1]) ((op == 2'b00) && (a == 4'b0000)) |-> (result == b)
    );

    // Subtraction identity: when op==01 and b==0, result equals a.
    check_subtraction_with_b_zero: assert property (
        @(posedge a[0] or posedge b[0] or posedge op[0] or posedge op[1]) ((op == 2'b01) && (b == 4'b0000)) |-> (result == a)
    );

    // Subtraction equality: when op==01 and a==b, result is 0.
    check_subtraction_equal_operands_zero: assert property (
        @(posedge a[0] or posedge b[0] or posedge op[0] or posedge op[1]) ((op == 2'b01) && (a == b)) |-> (result == 4'b0000)
    );

    // Functional mapping completeness: result matches the selected operation.
    check_functional_mapping_complete: assert property (
        @(posedge a[0] or posedge b[0] or posedge op[0] or posedge op[1])
            1'b1 |-> (
                ((op == 2'b00) && (result == (a + b)[3:0])) ||
                ((op == 2'b01) && (result == (a - b)[3:0])) ||
                ((op[1] == 1'b1) && (result == 4'b0000))
            )
    );
endmodule