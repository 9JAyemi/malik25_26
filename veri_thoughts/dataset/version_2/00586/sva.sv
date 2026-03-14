module alu_sva (
    input logic CLK,
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic op,
    input logic [15:0] out,
    input logic zero,
    input logic carry
);
    // When op==0, {carry,out} equals the 17-bit sum of in1 and in2.
    check_add_sum_selected: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 1'b0) |-> ({carry, out} == ({1'b0, in1} + {1'b0, in2}))
    );

    // When op==1, out equals bitwise NAND of inputs.
    check_nand_selected_out: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 1'b1) |-> (out == ~(in1 & in2))
    );

    // When op==1, carry is forced LOW.
    check_carry_zero_on_nand: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 1'b1) |-> (carry == 1'b0)
    );

    // zero is the NOR-reduction of out bits.
    check_zero_is_nor_out: assert property (
        @(posedge CLK) disable iff (1'b0) zero == ~(|out)
    );

    // For add op, zero matches NOR of expected sum low 16 bits.
    check_zero_matches_add: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 1'b0) |-> (zero == ~(|(({1'b0, in1} + {1'b0, in2})[15:0])))
    );

    // For NAND op, zero matches NOR of ~(in1 & in2).
    check_zero_matches_nand: assert property (
        @(posedge CLK) disable iff (1'b0) (op == 1'b1) |-> (zero == ~(|(~(in1 & in2))))
    );

    // If carry is HIGH, the operation must be add.
    check_carry_implies_add: assert property (
        @(posedge CLK) disable iff (1'b0) (carry == 1'b1) |-> (op == 1'b0)
    );

    // With stable inputs and op, outputs must remain stable.
    check_pure_comb_stability: assert property (
        @(posedge CLK) disable iff (1'b0) $stable({in1, in2, op}) |-> $stable({out, zero, carry})
    );
endmodule