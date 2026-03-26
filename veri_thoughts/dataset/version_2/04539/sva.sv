module cla32_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        ci,
    input logic [31:0] s,
    input logic        co
);

    // Outputs match 32-bit addition with carry-in.
    check_full_addition: assert property (
        @(posedge clk) {co, s} == ({1'b0, a} + {1'b0, b} + {{32{1'b0}}, ci})
    );

    // With carry-in low, outputs match a+b.
    check_addition_without_carry_in: assert property (
        @(posedge clk) (ci == 1'b0) |-> ({co, s} == ({1'b0, a} + {1'b0, b}))
    );

    // A zero operand passes b and carry-in through the adder.
    check_zero_a_operand: assert property (
        @(posedge clk) (a == 32'h0000_0000) |-> ({co, s} == ({1'b0, b} + {{32{1'b0}}, ci}))
    );

    // A zero operand on b passes a and carry-in through the adder.
    check_zero_b_operand: assert property (
        @(posedge clk) (b == 32'h0000_0000) |-> ({co, s} == ({1'b0, a} + {{32{1'b0}}, ci}))
    );

    // Zero plus zero produces only the carry-in in bit 0 and no carry-out.
    check_zero_inputs: assert property (
        @(posedge clk) ((a == 32'h0000_0000) && (b == 32'h0000_0000)) |-> (s == {31'd0, ci} && co == 1'b0)
    );

    // Sum bit 0 follows the full-adder equation.
    check_lsb_sum: assert property (
        @(posedge clk) s[0] == (a[0] ^ b[0] ^ ci)
    );

    // Sum bit 1 uses the carry generated from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) s[1] == (a[1] ^ b[1] ^ ((a[0] & b[0]) | ((a[0] | b[0]) & ci)))
    );

    // Disjoint one bits with no carry-in reduce to bitwise OR and no carry-out.
    check_disjoint_operands_no_carry: assert property (
        @(posedge clk) (((a & b) == 32'h0000_0000) && (ci == 1'b0)) |-> (s == (a | b) && co == 1'b0)
    );

    // Adding a value and its inverse with carry-in high wraps to zero with carry-out.
    check_inverse_operands_with_carry_in: assert property (
        @(posedge clk) ((b == ~a) && (ci == 1'b1)) |-> (s == 32'h0000_0000 && co == 1'b1)
    );

    // Adding a value and its inverse with carry-in low yields all ones and no carry-out.
    check_inverse_operands_without_carry_in: assert property (
        @(posedge clk) ((b == ~a) && (ci == 1'b0)) |-> (s == 32'hFFFF_FFFF && co == 1'b0)
    );

    // Stable inputs imply stable outputs for this combinational adder.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk) $stable({a, b, ci}) |-> $stable({s, co})
    );

endmodule