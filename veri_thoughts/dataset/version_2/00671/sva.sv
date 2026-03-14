module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_comb
);
    // Combinational DUT with no clock/reset; assertions sampled on clk.

    // Output equals RTL XOR expression.
    check_xor_equation: assert property (
        @(posedge clk) out_comb == ((a & ~b) | (~a & b))
    );

    // Output matches XOR operator directly.
    check_xor_operator_equiv: assert property (
        @(posedge clk) out_comb == (a ^ b)
    );

    // Truth table: a=0, b=0 -> out=0.
    check_tt_00: assert property (
        @(posedge clk) (!a && !b) |-> (out_comb == 1'b0)
    );

    // Truth table: a=1, b=0 -> out=1.
    check_tt_10: assert property (
        @(posedge clk) (a && !b) |-> (out_comb == 1'b1)
    );

    // Truth table: a=0, b=1 -> out=1.
    check_tt_01: assert property (
        @(posedge clk) (!a && b) |-> (out_comb == 1'b1)
    );

    // Truth table: a=1, b=1 -> out=0.
    check_tt_11: assert property (
        @(posedge clk) (a && b) |-> (out_comb == 1'b0)
    );

    // Output low when inputs are equal.
    check_equal_inputs_zero: assert property (
        @(posedge clk) (a == b) |-> (out_comb == 1'b0)
    );

    // Output high when inputs differ.
    check_diff_inputs_one: assert property (
        @(posedge clk) (a != b) |-> (out_comb == 1'b1)
    );

    // Commutative form equivalence.
    check_commutative_form: assert property (
        @(posedge clk) out_comb == ((b & ~a) | (~b & a))
    );
endmodule