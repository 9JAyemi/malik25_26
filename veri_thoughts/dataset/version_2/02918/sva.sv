module sky130_fd_sc_ls__o21bai_1_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);
    // Y matches the exact RTL ternary expression.
    check_functional_equivalence_ternary: assert property (
        @(posedge CLK) disable iff (1'b0)
            Y == ((B1_N == 1'b1) ? 1'b0
                 : ((A1 == 1'b1) ? 1'b1
                 : ((A2 == 1'b1) ? 1'b0 : 1'b1)))
    );

    // Y equals (~B1_N) & (A1 | ~A2).
    check_algebraic_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0)
            Y == ((~B1_N) & (A1 | ~A2))
    );

    // B1_N=1 forces Y=0.
    check_B1n_high_forces_Y_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
            (B1_N == 1'b1) |-> (Y == 1'b0)
    );

    // With B1_N=0 and A1=1, Y=1.
    check_B1n_low_A1_high_Y_one: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((B1_N == 1'b0) && (A1 == 1'b1)) |-> (Y == 1'b1)
    );

    // With B1_N=0, A1=0, and A2=1, Y=0.
    check_B1n_low_A1_low_A2_high_Y_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((B1_N == 1'b0) && (A1 == 1'b0) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // With B1_N=0 and A2=0, Y=1 regardless of A1.
    check_B1n_low_A2_low_Y_one: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((B1_N == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // With B1_N=0 and A2=1, Y equals A1.
    check_B1n_low_A2_high_Y_eq_A1: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((B1_N == 1'b0) && (A2 == 1'b1)) |-> (Y == A1)
    );

    // With B1_N=0 and A1=0, Y equals ~A2.
    check_B1n_low_A1_low_Y_eq_notA2: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((B1_N == 1'b0) && (A1 == 1'b0)) |-> (Y == (~A2))
    );

    // If Y=1 then B1_N=0 and (A1=1 or A2=0).
    check_Y_one_implies_inputs: assert property (
        @(posedge CLK) disable iff (1'b0)
            (Y == 1'b1) |-> ((B1_N == 1'b0) && ((A1 == 1'b1) || (A2 == 1'b0)))
    );

    // If Y=0 then B1_N=1 or (B1_N=0 and A1=0 and A2=1).
    check_Y_zero_implies_inputs: assert property (
        @(posedge CLK) disable iff (1'b0)
            (Y == 1'b0) |-> ((B1_N == 1'b1) || ((B1_N == 1'b0) && (A1 == 1'b0) && (A2 == 1'b1)))
    );
endmodule