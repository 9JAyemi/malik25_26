module my_or_gate_sva (
    input logic A,
    input logic B,
    input logic C_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
    // X implements B & (A | C_N) (sampled on A rising).
    check_function_equivalence_on_A: assert property (
        @(posedge A) X == ((A & B) | (B & C_N))
    );

    // X implements B & (A | C_N) (sampled on B rising).
    check_function_equivalence_on_B: assert property (
        @(posedge B) X == ((A & B) | (B & C_N))
    );

    // X implements B & (A | C_N) (sampled on C_N rising).
    check_function_equivalence_on_CN: assert property (
        @(posedge C_N) X == ((A & B) | (B & C_N))
    );

    // When B is 0, X must be 0 (sampled on A rising).
    check_b_zero_forces_x_zero_on_A: assert property (
        @(posedge A) (B == 1'b0) |-> (X == 1'b0)
    );

    // When B is 0, X must be 0 (sampled on B rising).
    check_b_zero_forces_x_zero_on_B: assert property (
        @(posedge B) (B == 1'b0) |-> (X == 1'b0)
    );

    // When B is 0, X must be 0 (sampled on C_N rising).
    check_b_zero_forces_x_zero_on_CN: assert property (
        @(posedge C_N) (B == 1'b0) |-> (X == 1'b0)
    );

    // When B is 1, X equals A OR C_N (sampled on A rising).
    check_b_one_reduces_to_or_on_A: assert property (
        @(posedge A) (B == 1'b1) |-> (X == (A | C_N))
    );

    // When B is 1, X equals A OR C_N (sampled on B rising).
    check_b_one_reduces_to_or_on_B: assert property (
        @(posedge B) (B == 1'b1) |-> (X == (A | C_N))
    );

    // X can be 1 only if B==1 and (A==1 or C_N==1) (sampled on A rising).
    check_x_one_implies_conditions_on_A: assert property (
        @(posedge A) (X == 1'b1) |-> (B == 1'b1 && ((A == 1'b1) || (C_N == 1'b1)))
    );

    // If A==0 and C_N==0, X must be 0 (sampled on B rising).
    check_a0_cn0_forces_x0_on_B: assert property (
        @(posedge B) ((A == 1'b0) && (C_N == 1'b0)) |-> (X == 1'b0)
    );
endmodule