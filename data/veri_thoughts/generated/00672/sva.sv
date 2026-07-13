module alu_sva (
    input logic clk,
    input logic [31:0] a_in,
    input logic [31:0] b_in,
    input logic [3:0]  alu_function,
    input logic [31:0] c_alu
);
    // For alu_add (0001), output equals lower 32 bits of sign-extended 33-bit a_in + b_in.
    check_add_lower32_from_signext_add: assert property (
        @(posedge clk) disable iff (1'b0)
            (alu_function == 4'b0001) |-> (c_alu == (({a_in[31], a_in} + {b_in[31], b_in})[31:0]))
    );

    // For alu_add (0001), output equals 32-bit a_in + b_in (ignoring carry-out).
    check_add_32bit_equivalence: assert property (
        @(posedge clk) disable iff (1'b0)
            (alu_function == 4'b0001) |-> (c_alu == (a_in + b_in))
    );

    // For alu_less_than (0010), output is 1 when a_in < b_in (unsigned) and zero otherwise.
    check_less_than_unsigned: assert property (
        @(posedge clk) disable iff (1'b0)
            (alu_function == 4'b0010) |-> ((c_alu[31:1] == 31'b0) && (c_alu[0] == (a_in < b_in)))
    );

    // For alu_less_than (0010), LSB equals borrow of zero-extended subtraction a_in - b_in.
    check_less_than_borrow_equals_lsb: assert property (
        @(posedge clk) disable iff (1'b0)
            (alu_function == 4'b0010) |-> (c_alu[0] == (({1'b0, a_in} - {1'b0, b_in})[32]))
    );

    // For alu_or (0100), output equals a_in | b_in.
    check_or_result: assert property (
        @(posedge clk) disable iff (1'b0)
            (alu_function == 4'b0100) |-> (c_alu == (a_in | b_in))
    );

    // For alu_and (0101), output equals a_in & b_in.
    check_and_result: assert property (
        @(posedge clk) disable iff (1'b0)
            (alu_function == 4'b0101) |-> (c_alu == (a_in & b_in))
    );

    // For alu_xor (0110), output equals a_in ^ b_in.
    check_xor_result: assert property (
        @(posedge clk) disable iff (1'b0)
            (alu_function == 4'b0110) |-> (c_alu == (a_in ^ b_in))
    );

    // For alu_nor (0111), output equals ~(a_in | b_in).
    check_nor_result: assert property (
        @(posedge clk) disable iff (1'b0)
            (alu_function == 4'b0111) |-> (c_alu == ~(a_in | b_in))
    );

    // For all other opcodes, output is zero.
    check_default_zero: assert property (
        @(posedge clk) disable iff (1'b0)
            (!(alu_function inside {4'b0001,4'b0010,4'b0100,4'b0101,4'b0110,4'b0111})) |-> (c_alu == 32'b0)
    );
endmodule