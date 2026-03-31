module alu_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [2:0] op,
    input logic [3:0] out
);

    // op 000 selects 4-bit addition.
    check_addition: assert property (
        @(posedge clk) (op == 3'b000) |-> (out == (a + b))
    );

    // op 001 selects 4-bit subtraction.
    check_subtraction: assert property (
        @(posedge clk) (op == 3'b001) |-> (out == (a - b))
    );

    // op 010 selects bitwise AND.
    check_and: assert property (
        @(posedge clk) (op == 3'b010) |-> (out == (a & b))
    );

    // op 011 selects bitwise OR.
    check_or: assert property (
        @(posedge clk) (op == 3'b011) |-> (out == (a | b))
    );

    // op 100 selects bitwise XOR.
    check_xor: assert property (
        @(posedge clk) (op == 3'b100) |-> (out == (a ^ b))
    );

    // op 101 selects a left shift by one bit.
    check_shift_left: assert property (
        @(posedge clk) (op == 3'b101) |-> (out == {a[2:0], 1'b0})
    );

    // op values 110 and 111 drive the default zero output.
    check_default_zero: assert property (
        @(posedge clk) ((op == 3'b110) || (op == 3'b111)) |-> (out == 4'b0000)
    );

endmodule