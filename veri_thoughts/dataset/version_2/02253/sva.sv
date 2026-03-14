module alu_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [2:0] op,
    input logic [3:0] out
);
    // When op==000, out equals a + b (truncated to 4 bits).
    check_addition: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 3'b000) |-> (out == (a + b))
    );

    // When op==001, out equals a - b (truncated to 4 bits).
    check_subtraction: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 3'b001) |-> (out == (a - b))
    );

    // When op==010, out equals a & b.
    check_bitwise_and: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 3'b010) |-> (out == (a & b))
    );

    // When op==011, out equals a | b.
    check_bitwise_or: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 3'b011) |-> (out == (a | b))
    );

    // When op==100, out equals a ^ b.
    check_bitwise_xor: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 3'b100) |-> (out == (a ^ b))
    );

    // When op==101, out equals {a[2:0], 1'b0} (shift left by 1 with zero fill).
    check_shift_left: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 3'b101) |-> (out == {a[2:0], 1'b0})
    );

    // When op is 110 or 111, out is 0 (default case).
    check_default_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (op inside {3'b110, 3'b111}) |-> (out == 4'b0000)
    );
endmodule