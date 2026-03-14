module sky130_fd_sc_hd__nand2b_sva (
    input logic Y,
    input logic A_N,
    input logic B
);
    // No clock/reset in DUT; pure combinational; function: Y = A_N | ~B.

    // Y equals A_N | ~B on A_N rising edge.
    check_function_equiv_posA: assert property (
        @(posedge A_N) (Y === (A_N | ~B))
    );

    // Y equals A_N | ~B on A_N falling edge.
    check_function_equiv_negA: assert property (
        @(negedge A_N) (Y === (A_N | ~B))
    );

    // Y equals A_N | ~B on B rising edge.
    check_function_equiv_posB: assert property (
        @(posedge B) (Y === (A_N | ~B))
    );

    // Y equals A_N | ~B on B falling edge.
    check_function_equiv_negB: assert property (
        @(negedge B) (Y === (A_N | ~B))
    );

    // A_N=1 forces Y=1 on A_N rising edge.
    check_A_N_one_forces_Y_one_posA: assert property (
        @(posedge A_N) (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // A_N=1 forces Y=1 on A_N falling edge.
    check_A_N_one_forces_Y_one_negA: assert property (
        @(negedge A_N) (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // B=0 forces Y=1 on B rising edge.
    check_B_zero_forces_Y_one_posB: assert property (
        @(posedge B) (B == 1'b0) |-> (Y == 1'b1)
    );

    // B=0 forces Y=1 on B falling edge.
    check_B_zero_forces_Y_one_negB: assert property (
        @(negedge B) (B == 1'b0) |-> (Y == 1'b1)
    );

    // Y==0 iff (A_N==0 && B==1) on A_N rising edge.
    check_only_zero_case_posA: assert property (
        @(posedge A_N) ((Y === 1'b0) == ((A_N === 1'b0) && (B === 1'b1)))
    );

    // Y==0 iff (A_N==0 && B==1) on B rising edge.
    check_only_zero_case_posB: assert property (
        @(posedge B) ((Y === 1'b0) == ((A_N === 1'b0) && (B === 1'b1)))
    );
endmodule