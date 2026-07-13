module ripple_carry_adder_sva(
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] SUM,
    input logic COUT
);

    // Full 5-bit result matches A + B + CIN.
    check_total_addition: assert property (
        @(posedge clk)
        {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {4'b0, CIN})
    );

    // LSB sum matches the first full-adder XOR equation.
    check_lsb_xor: assert property (
        @(posedge clk)
        SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    // Carry-out matches arithmetic overflow.
    check_cout_overflow: assert property (
        @(posedge clk)
        COUT == (({1'b0, A} + {1'b0, B} + {4'b0, CIN}) >= 5'd16)
    );

    // Adding zero with no carry-in preserves A.
    check_add_zero_to_a: assert property (
        @(posedge clk)
        (B == 4'h0 && CIN == 1'b0) |-> (SUM == A && COUT == 1'b0)
    );

    // Adding zero with no carry-in preserves B.
    check_add_zero_to_b: assert property (
        @(posedge clk)
        (A == 4'h0 && CIN == 1'b0) |-> (SUM == B && COUT == 1'b0)
    );

    // With zero operands, only CIN contributes to the result.
    check_zero_operands_with_cin: assert property (
        @(posedge clk)
        (A == 4'h0 && B == 4'h0) |-> (SUM == {3'b000, CIN} && COUT == 1'b0)
    );

    // A carry-in can ripple through all four stages.
    check_full_carry_propagation: assert property (
        @(posedge clk)
        (A == 4'hF && B == 4'h0 && CIN == 1'b1) |-> (SUM == 4'h0 && COUT == 1'b1)
    );

    // Stable sampled inputs must keep sampled outputs stable.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk)
        $stable({A, B, CIN}) |-> $stable({SUM, COUT})
    );

endmodule