module add_sub_4bit_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       mode,
    input logic [3:0] sum,
    input logic       carry_borrow
);

    // Sum matches 4-bit addition when mode selects add.
    check_add_mode_sum: assert property (
        @(posedge clk) (!mode) |-> (sum == (A + B))
    );

    // Sum matches 4-bit subtraction when mode selects subtract.
    check_sub_mode_sum: assert property (
        @(posedge clk) mode |-> (sum == (A - B))
    );

    // Sum always matches the selected 4-bit arithmetic operation.
    check_selected_operation_sum: assert property (
        @(posedge clk) sum == (mode ? (A - B) : (A + B))
    );

    // carry_borrow is always low in this implementation.
    check_carry_borrow_always_low: assert property (
        @(posedge clk) carry_borrow == 1'b0
    );

    // Adding zero on B leaves A unchanged.
    check_add_zero_b: assert property (
        @(posedge clk) (!mode && (B == 4'h0)) |-> (sum == A)
    );

    // Adding zero on A leaves B unchanged.
    check_add_zero_a: assert property (
        @(posedge clk) (!mode && (A == 4'h0)) |-> (sum == B)
    );

    // Subtracting zero leaves A unchanged.
    check_sub_zero_b: assert property (
        @(posedge clk) (mode && (B == 4'h0)) |-> (sum == A)
    );

    // Subtracting equal operands yields zero.
    check_sub_equal_operands: assert property (
        @(posedge clk) (mode && (A == B)) |-> (sum == 4'h0)
    );

    // Addition overflow wraps in 4 bits and does not raise carry_borrow.
    check_add_overflow_wrap: assert property (
        @(posedge clk) (!mode && (A == 4'hF) && (B == 4'h1)) |-> ((sum == 4'h0) && (carry_borrow == 1'b0))
    );

    // Subtraction underflow wraps in 4 bits and does not raise carry_borrow.
    check_sub_underflow_wrap: assert property (
        @(posedge clk) (mode && (A == 4'h0) && (B == 4'h1)) |-> ((sum == 4'hF) && (carry_borrow == 1'b0))
    );

endmodule