module sky130_fd_sc_ls__or3b_sva (
    input  logic CLK,
    input  logic X,
    input  logic A,
    input  logic B,
    input  logic C_N
);
    // X must equal A | B | ~C_N.
    check_x_functional_equivalence: assert property (
        @(posedge CLK) X === (A | B | ~C_N)
    );

    // If A is 1 then X must be 1.
    check_x_high_when_A_high: assert property (
        @(posedge CLK) (A === 1'b1) |-> (X === 1'b1)
    );

    // If B is 1 then X must be 1.
    check_x_high_when_B_high: assert property (
        @(posedge CLK) (B === 1'b1) |-> (X === 1'b1)
    );

    // If C_N is 0 then X must be 1.
    check_x_high_when_C_N_low: assert property (
        @(posedge CLK) (C_N === 1'b0) |-> (X === 1'b1)
    );

    // If A=0, B=0, and C_N=1 then X must be 0.
    check_x_low_when_all_inactive: assert property (
        @(posedge CLK) ((A === 1'b0) && (B === 1'b0) && (C_N === 1'b1)) |-> (X === 1'b0)
    );

    // If X is 0 then A=0, B=0, and C_N=1.
    check_inputs_when_x_low: assert property (
        @(posedge CLK) (X === 1'b0) |-> ((A === 1'b0) && (B === 1'b0) && (C_N === 1'b1))
    );

    // If X is 1 then (A=1 or B=1 or C_N=0).
    check_inputs_when_x_high: assert property (
        @(posedge CLK) (X === 1'b1) |-> ((A === 1'b1) || (B === 1'b1) || (C_N === 1'b0))
    );

    // With stable inputs across a cycle, X remains stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(C_N)) |-> $stable(X)
    );
endmodule