module bitwise_operations_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [1:0]  operation_select,
    input logic [4:0]  shift_amount,
    input logic [31:0] result
);

// AND selected returns a & b.
    check_and_select: assert property (
        @(posedge clk) (operation_select == 2'b00) |-> (result == (a & b))
    );

// OR selected returns a | b.
    check_or_select: assert property (
        @(posedge clk) (operation_select == 2'b01) |-> (result == (a | b))
    );

// XOR selected returns a ^ b.
    check_xor_select: assert property (
        @(posedge clk) (operation_select == 2'b10) |-> (result == (a ^ b))
    );

// Shift selected returns a << shift_amount.
    check_shift_select: assert property (
        @(posedge clk) (operation_select == 2'b11) |-> (result == (a << shift_amount))
    );

// AND result has bits not in both inputs cleared.
    check_and_result_subset: assert property (
        @(posedge clk) (operation_select == 2'b00) |-> ((result & ~(a & b)) == 32'h0000_0000)
    );

// OR result has bits in either input set.
    check_or_result_superset: assert property (
        @(posedge clk) (operation_select == 2'b01) |-> ((result & ~(a | b)) == 32'h0000_0000)
    );

// XOR result has bits in exactly one input set.
    check_xor_result_exclusive: assert property (
        @(posedge clk) (operation_select == 2'b10) |-> ((result & (a & b)) == 32'h0000_0000)
    );

// Shift result has the shifted-in bits in the low bits.
    check_shift_result_low_bits: assert property (
        @(posedge clk) (operation_select == 2'b11) |-> ((result & ~(32'h0000_0001 << shift_amount)) == 32'h0000_0000)
    );

// Shift result has zero in the vacated high bits.
    check_shift_result_high_bits_zero: assert property (
        @(posedge clk) (operation_select == 2'b11) |-> ((result & (32'h0000_0001 << (shift_amount + 5'd1))) == 32'h0000_0000)
    );

endmodule
