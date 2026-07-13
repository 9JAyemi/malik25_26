module alu_sva (
    input logic [3:0] alu_ctl,
    input signed [31:0] A, B,
    input logic zero,
    input logic [31:0] result
);
    // Zero flag is set when the result is zero
    zero_flag: assert property (
        @(posedge clk) disable iff (!resetn) zero |-> (result == 0)
    );

    // Addition operation
    add_operation: assert property (
        @(posedge clk) disable iff (!resetn) (alu_ctl == 4'b0001) |-> (result == A + B)
    );

    // Subtraction operation
    sub_operation: assert property (
        @(posedge clk) disable iff (!resetn) (alu_ctl == 4'b0010) |-> (result == A - B)
    );

    // AND operation
    and_operation: assert property (
        @(posedge clk) disable iff (!resetn) (alu_ctl == 4'b0011) |-> (result == A & B)
    );

    // OR operation
    or_operation: assert property (
        @(posedge clk) disable iff (!resetn) (alu_ctl == 4'b0100) |-> (result == A | B)
    );

    // XOR operation
    xor_operation: assert property (
        @(posedge clk) disable iff (!resetn) (alu_ctl == 4'b0101) |-> (result == A ^ B)
    );

    // NOR operation
    nor_operation: assert property (
        @(posedge clk) disable iff (!resetn) (alu_ctl == 4'b0110) |-> (result == ~(A | B))
    );

    // Right shift operation
    right_shift_operation: assert property (
        @(posedge clk) disable iff (!resetn) (alu_ctl == 4'b0111) |-> (result == B >> 1)
    );

    // Sign extend operation
    sign_extend_operation: assert property (
        @(posedge clk) disable iff (!resetn) (alu_ctl == 4'b1000) |-> (result == {B[15:0], 16'b0})
    );

    // Less than operation
    less_than_operation: assert property (
        @(posedge clk) disable iff (!resetn) (alu_ctl == 4'b1001) |-> (result == (A < B))
    );
endmodule