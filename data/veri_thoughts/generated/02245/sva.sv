module sky130_fd_sc_ls__o32ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // Clocking on any input edge to sample combinational behavior
    // (module has no explicit clock/reset)
    // Helper macros to represent group ORs
    `define A_OR   (A1 || A2 || A3)
    `define B_OR   (B1 || B2)
    `define COMB_EVT (posedge A1 or negedge A1 or \
                      posedge A2 or negedge A2 or \
                      posedge A3 or negedge A3 or \
                      posedge B1 or negedge B1 or \
                      posedge B2 or negedge B2)

    ///// Functional equivalence /////
    // Y equals (~(A1|A2|A3)) | (~(B1|B2)).
    check_func_or_nor_form: assert property (
        @(`COMB_EVT) Y == ((~(`A_OR)) | (~(`B_OR)))
    );
    // Y equals ~((A1|A2|A3) & (B1|B2)).
    check_func_nand_form: assert property (
        @(`COMB_EVT) Y == ~( (`A_OR) & (`B_OR) )
    );

    ///// Derived implications /////
    // If all A inputs are LOW, Y must be HIGH.
    check_all_A_low_implies_Y_high: assert property (
        @(`COMB_EVT) (~(`A_OR)) |-> (Y == 1'b1)
    );
    // If all B inputs are LOW, Y must be HIGH.
    check_all_B_low_implies_Y_high: assert property (
        @(`COMB_EVT) (~(`B_OR)) |-> (Y == 1'b1)
    );
    // If at least one A and at least one B are HIGH, Y must be LOW.
    check_any_A_and_any_B_high_implies_Y_low: assert property (
        @(`COMB_EVT) ((`A_OR) && (`B_OR)) |-> (Y == 1'b0)
    );
    // If A group OR is LOW and B group OR is HIGH, Y must be HIGH.
    check_A_group_low_B_group_high_implies_Y_high: assert property (
        @(`COMB_EVT) ((~(`A_OR)) && (`B_OR)) |-> (Y == 1'b1)
    );
    // If B group OR is LOW and A group OR is HIGH, Y must be HIGH.
    check_B_group_low_A_group_high_implies_Y_high: assert property (
        @(`COMB_EVT) ((~(`B_OR)) && (`A_OR)) |-> (Y == 1'b1)
    );
    // If all five inputs are LOW, Y must be HIGH.
    check_all_inputs_low_implies_Y_high: assert property (
        @(`COMB_EVT) ((A1==1'b0)&&(A2==1'b0)&&(A3==1'b0)&&(B1==1'b0)&&(B2==1'b0)) |-> (Y==1'b1)
    );
    // If any A is HIGH and any B is HIGH, Y must be LOW (explicit variant).
    check_explicit_pair_high_implies_Y_low: assert property (
        @(`COMB_EVT) ((A1||A2||A3) && (B1||B2)) |-> (Y==1'b0)
    );

    // Clean up macros
    `undef A_OR
    `undef B_OR
    `undef COMB_EVT
endmodule