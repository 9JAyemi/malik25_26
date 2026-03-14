module sky130_fd_sc_ls__o221ai_sva (
    // DUT ports
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    // Sampling clock for SVA (DUT has no clock/reset)
    input logic CLK
);
    // No clock or reset in RTL; pure combinational. Sample assertions on CLK.
    // Function: Y = ~((A1|A2) & (B1|B2) & C1)

    // Output equals the specified O221AI boolean function.
    check_function_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0)
            Y == ~(((A1 | A2) & (B1 | B2) & C1))
    );

    // If C1 is 0, the NAND input product is 0, so Y must be 1.
    check_C1_low_forces_Y_high: assert property (
        @(posedge CLK) disable iff (1'b0)
            (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // If both A inputs are 0, the A-group OR is 0, so Y must be 1.
    check_A_group_zero_forces_Y_high: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // If both B inputs are 0, the B-group OR is 0, so Y must be 1.
    check_B_group_zero_forces_Y_high: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );

    // If all three terms are 1, NAND output is 0, so Y must be 0.
    check_all_terms_high_forces_Y_low: assert property (
        @(posedge CLK) disable iff (1'b0)
            (C1 && (A1 | A2) && (B1 | B2)) |-> (Y == 1'b0)
    );

    // With C1==1 and A-group OR==1, Y equals bitwise NOT of B-group OR.
    check_decompose_with_C1_and_Agrp1: assert property (
        @(posedge CLK) disable iff (1'b0)
            (C1 && (A1 | A2)) |-> (Y == ~(B1 | B2))
    );

    // With C1==1 and B-group OR==1, Y equals bitwise NOT of A-group OR.
    check_decompose_with_C1_and_Bgrp1: assert property (
        @(posedge CLK) disable iff (1'b0)
            (C1 && (B1 | B2)) |-> (Y == ~(A1 | A2))
    );

    // De Morgan equivalent form must also hold.
    check_demorgan_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0)
            Y == ((~C1) | (~(A1 | A2)) | (~(B1 | B2)))
    );
endmodule