module calculator_sva (
    input logic signed [7:0] A,
    input logic signed [7:0] B,
    input logic [1:0] Op,
    input logic signed [7:0] C
);
    typedef logic signed [7:0] s8_t;

    // No RTL clock or reset; sample combinational behavior on the global formal clock.

    // Op 00 selects signed addition.
    check_add_operation: assert property (
        @($global_clock)
        (Op == 2'b00) |-> (C == s8_t'(A + B))
    );

    // Op 01 selects signed subtraction.
    check_sub_operation: assert property (
        @($global_clock)
        (Op == 2'b01) |-> (C == s8_t'(A - B))
    );

    // Op 10 selects signed multiplication with 8-bit truncation.
    check_mul_operation: assert property (
        @($global_clock)
        (Op == 2'b10) |-> (C == s8_t'(A * B))
    );

    // Op 11 selects signed division when the divisor is nonzero.
    check_div_operation_nonzero_divisor: assert property (
        @($global_clock)
        ((Op == 2'b11) && (B != 8'sd0)) |-> (C == s8_t'(A / B))
    );

endmodule