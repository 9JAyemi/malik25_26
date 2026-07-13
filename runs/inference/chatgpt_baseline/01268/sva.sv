module half_adder_sva (
    input logic clk,        // external sampling clock (RTL is purely combinational; no reset)
    input logic A,
    input logic B,
    input logic sum,
    input logic carry_out
);
    // sum equals A XOR B.
    check_sum_is_xor: assert property (
        @(posedge clk) disable iff (1'b0) sum == (A ^ B)
    );

    // carry_out equals A AND B.
    check_carry_is_and: assert property (
        @(posedge clk) disable iff (1'b0) carry_out == (A & B)
    );

    // sum and carry_out are never both HIGH.
    check_sum_carry_mutex: assert property (
        @(posedge clk) disable iff (1'b0) !(sum && carry_out)
    );

    // (sum OR carry_out) equals (A OR B).
    check_or_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) (sum | carry_out) == (A | B)
    );

    // For A=0,B=0: sum=0 and carry_out=0.
    check_tt_00: assert property (
        @(posedge clk) disable iff (1'b0) ((A==1'b0) && (B==1'b0)) |-> ((sum==1'b0) && (carry_out==1'b0))
    );

    // For A=1,B=1: sum=0 and carry_out=1.
    check_tt_11: assert property (
        @(posedge clk) disable iff (1'b0) ((A==1'b1) && (B==1'b1)) |-> ((sum==1'b0) && (carry_out==1'b1))
    );

    // If carry_out is HIGH then both inputs are HIGH.
    check_carry_implies_inputs_high: assert property (
        @(posedge clk) disable iff (1'b0) carry_out |-> (A && B)
    );

    // If sum is HIGH then inputs differ.
    check_sum_implies_inputs_differ: assert property (
        @(posedge clk) disable iff (1'b0) sum |-> (A ^ B)
    );

    // {carry_out,sum} equals zero-extended A+B.
    check_addition_identity: assert property (
        @(posedge clk) disable iff (1'b0) {carry_out, sum} == ({1'b0, A} + {1'b0, B})
    );
endmodule