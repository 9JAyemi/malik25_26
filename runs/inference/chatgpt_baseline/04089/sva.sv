module binary_adder_sva(
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        CIN,
    input logic [3:0]  SUM,
    input logic        COUT
);

    // The 5-bit output must equal A + B + CIN.
    check_total_addition: assert property (
        @(posedge clk)
        {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {4'b0000, CIN})
    );

    // The least-significant sum bit matches the first full-adder XOR.
    check_lsb_sum: assert property (
        @(posedge clk)
        SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    // Carry-out reflects overflow of the 4-bit addition.
    check_cout_overflow: assert property (
        @(posedge clk)
        COUT == (({1'b0, A} + {1'b0, B} + {4'b0000, CIN}) > 5'd15)
    );

    // With no carry-in, the result matches A + B.
    check_add_without_cin: assert property (
        @(posedge clk)
        !CIN |-> ({COUT, SUM} == ({1'b0, A} + {1'b0, B}))
    );

    // With carry-in asserted, the result matches A + B + 1.
    check_add_with_cin: assert property (
        @(posedge clk)
        CIN |-> ({COUT, SUM} == ({1'b0, A} + {1'b0, B} + 5'b00001))
    );

    // Adding zero to A with no carry-in returns A and no carry-out.
    check_a_identity: assert property (
        @(posedge clk)
        (B == 4'b0000 && !CIN) |-> (SUM == A && COUT == 1'b0)
    );

    // Adding zero to B with no carry-in returns B and no carry-out.
    check_b_identity: assert property (
        @(posedge clk)
        (A == 4'b0000 && !CIN) |-> (SUM == B && COUT == 1'b0)
    );

    // Zero plus zero produces only the carry-in in the result.
    check_zero_inputs: assert property (
        @(posedge clk)
        (A == 4'b0000 && B == 4'b0000) |-> ({COUT, SUM} == {4'b0000, CIN})
    );

    // A carry-in propagates through all bits when the other operand is all ones.
    check_cin_propagation: assert property (
        @(posedge clk)
        (((A == 4'hF) && (B == 4'h0) && (CIN == 1'b1)) ||
         ((A == 4'h0) && (B == 4'hF) && (CIN == 1'b1)))
        |-> (SUM == 4'h0 && COUT == 1'b1)
    );

    // Maximum inputs with carry-in overflow and leave SUM at all ones.
    check_max_input_overflow: assert property (
        @(posedge clk)
        (A == 4'hF && B == 4'hF && CIN == 1'b1) |-> (SUM == 4'hF && COUT == 1'b1)
    );

endmodule