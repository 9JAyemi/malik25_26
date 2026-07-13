module sky130_fd_sc_ms__nand4bb_sva (
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic nand0_out,
    input logic or0_out_Y
);
    // No explicit clock/reset in RTL; combinational cell sampled on any input/output edge.

    // Y equals A_N | B_N | ~(C & D).
    check_function_y: assert property (
        @(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
        Y === (A_N | B_N | ~(C & D))
    );

    // nand0_out equals ~(D & C).
    check_nand0_equation: assert property (
        @(posedge C or negedge C or posedge D or negedge D or posedge nand0_out or negedge nand0_out)
        nand0_out === ~(D & C)
    );

    // or0_out_Y equals B_N | A_N | nand0_out.
    check_or0_equation: assert property (
        @(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge nand0_out or negedge nand0_out or posedge or0_out_Y or negedge or0_out_Y)
        or0_out_Y === (B_N | A_N | nand0_out)
    );

    // Buffer drives Y equal to or0_out_Y.
    check_buf_equation: assert property (
        @(posedge Y or negedge Y or posedge or0_out_Y or negedge or0_out_Y)
        Y === or0_out_Y
    );

    // A_N high forces Y high.
    check_A_N_dominates: assert property (
        @(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
        (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // B_N high forces Y high.
    check_B_N_dominates: assert property (
        @(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
        (B_N == 1'b1) |-> (Y == 1'b1)
    );

    // C low forces Y high.
    check_C_zero_dominates: assert property (
        @(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
        (C == 1'b0) |-> (Y == 1'b1)
    );

    // D low forces Y high.
    check_D_zero_dominates: assert property (
        @(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
        (D == 1'b0) |-> (Y == 1'b1)
    );

    // When A_N=0, B_N=0, C=1, D=1, Y must be 0.
    check_zero_condition: assert property (
        @(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
        ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b1) && (D == 1'b1)) |-> (Y == 1'b0)
    );

    // Y can be 0 only if A_N=0, B_N=0, C=1, D=1.
    check_y_zero_implies_inputs: assert property (
        @(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge C or negedge C or posedge D or negedge D or posedge Y or negedge Y)
        (Y == 1'b0) |-> ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b1) && (D == 1'b1))
    );

    // With A_N=0 and B_N=0, or0_out_Y equals nand0_out.
    check_or_passthrough_when_AB_low: assert property (
        @(posedge A_N or negedge A_N or posedge B_N or negedge B_N or posedge nand0_out or negedge nand0_out or posedge or0_out_Y or negedge or0_out_Y)
        ((A_N == 1'b0) && (B_N == 1'b0)) |-> (or0_out_Y === nand0_out)
    );

    // If both C and D are 1, nand0_out is 0.
    check_nand_low_when_CD_high: assert property (
        @(posedge C or negedge C or posedge D or negedge D or posedge nand0_out or negedge nand0_out)
        ((C == 1'b1) && (D == 1'b1)) |-> (nand0_out == 1'b0)
    );

    // If either C or D is 0, nand0_out is 1.
    check_nand_high_when_any_CD_low: assert property (
        @(posedge C or negedge C or posedge D or negedge D or posedge nand0_out or negedge nand0_out)
        ((C == 1'b0) || (D == 1'b0)) |-> (nand0_out == 1'b1)
    );
endmodule