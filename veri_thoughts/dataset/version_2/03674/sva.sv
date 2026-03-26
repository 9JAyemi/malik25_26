module sky130_fd_sc_ls__xor3_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // Output equals the three-input XOR of A, B, and C.
    check_x_matches_xor3_function: assert property (
        @(posedge clk) X === (A ^ B ^ C)
    );

    // When A and B are equal known bits, output matches C.
    check_ab_equal_output_matches_c: assert property (
        @(posedge clk)
        (((A === 1'b0) && (B === 1'b0)) || ((A === 1'b1) && (B === 1'b1)))
        |-> (X === C)
    );

    // When A and B differ as known bits, output inverts C.
    check_ab_different_output_inverts_c: assert property (
        @(posedge clk)
        (((A === 1'b0) && (B === 1'b1)) || ((A === 1'b1) && (B === 1'b0)))
        |-> (X === ~C)
    );

    // When B and C are equal known bits, output matches A.
    check_bc_equal_output_matches_a: assert property (
        @(posedge clk)
        (((B === 1'b0) && (C === 1'b0)) || ((B === 1'b1) && (C === 1'b1)))
        |-> (X === A)
    );

    // When B and C differ as known bits, output inverts A.
    check_bc_different_output_inverts_a: assert property (
        @(posedge clk)
        (((B === 1'b0) && (C === 1'b1)) || ((B === 1'b1) && (C === 1'b0)))
        |-> (X === ~A)
    );

    // When A and C are equal known bits, output matches B.
    check_ac_equal_output_matches_b: assert property (
        @(posedge clk)
        (((A === 1'b0) && (C === 1'b0)) || ((A === 1'b1) && (C === 1'b1)))
        |-> (X === B)
    );

    // When A and C differ as known bits, output inverts B.
    check_ac_different_output_inverts_b: assert property (
        @(posedge clk)
        (((A === 1'b0) && (C === 1'b1)) || ((A === 1'b1) && (C === 1'b0)))
        |-> (X === ~B)
    );

endmodule