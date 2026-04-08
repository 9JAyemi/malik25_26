module priority_mux_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [3:0]  C,
    input logic [3:0]  D,
    input logic [1:0]  S,
    input logic        Y,
    input logic        Z
);

    // Y and Z are never driven high together.
    check_outputs_not_both_high: assert property (
        @(posedge clk) !(Y && Z)
    );

    // For S=00, any nonzero A selects Y=1 and Z=0.
    check_sel00_a_priority: assert property (
        @(posedge clk)
        (S == 2'b00 && (A != 4'b0000)) |-> (Y == 1'b1 && Z == 1'b0)
    );

    // For S=00, B selects Y=0 and Z=1 when A is zero.
    check_sel00_b_priority: assert property (
        @(posedge clk)
        (S == 2'b00 && (A == 4'b0000) && (B != 4'b0000)) |-> (Y == 1'b0 && Z == 1'b1)
    );

    // For S=00, outputs are 0 when both A and B are zero.
    check_sel00_default_zero: assert property (
        @(posedge clk)
        (S == 2'b00 && (A == 4'b0000) && (B == 4'b0000)) |-> (Y == 1'b0 && Z == 1'b0)
    );

    // For S=01, any nonzero B selects Y=0 and Z=1.
    check_sel01_b_priority: assert property (
        @(posedge clk)
        (S == 2'b01 && (B != 4'b0000)) |-> (Y == 1'b0 && Z == 1'b1)
    );

    // For S=01, A selects Y=1 and Z=0 when B is zero.
    check_sel01_a_priority: assert property (
        @(posedge clk)
        (S == 2'b01 && (B == 4'b0000) && (A != 4'b0000)) |-> (Y == 1'b1 && Z == 1'b0)
    );

    // For S=01, outputs are 0 when both B and A are zero.
    check_sel01_default_zero: assert property (
        @(posedge clk)
        (S == 2'b01 && (B == 4'b0000) && (A == 4'b0000)) |-> (Y == 1'b0 && Z == 1'b0)
    );

    // For S=10, any nonzero C forces both outputs low.
    check_sel10_c_priority: assert property (
        @(posedge clk)
        (S == 2'b10 && (C != 4'b0000)) |-> (Y == 1'b0 && Z == 1'b0)
    );

    // For S=10, A selects Y=1 and Z=0 when C is zero.
    check_sel10_a_priority: assert property (
        @(posedge clk)
        (S == 2'b10 && (C == 4'b0000) && (A != 4'b0000)) |-> (Y == 1'b1 && Z == 1'b0)
    );

    // For S=10, B selects Y=0 and Z=1 when C and A are zero.
    check_sel10_b_priority: assert property (
        @(posedge clk)
        (S == 2'b10 && (C == 4'b0000) && (A == 4'b0000) && (B != 4'b0000)) |-> (Y == 1'b0 && Z == 1'b1)
    );

    // For S=10, outputs are 0 when C, A, and B are all zero.
    check_sel10_default_zero: assert property (
        @(posedge clk)
        (S == 2'b10 && (C == 4'b0000) && (A == 4'b0000) && (B == 4'b0000)) |-> (Y == 1'b0 && Z == 1'b0)
    );

    // For S=11, any nonzero D forces both outputs low.
    check_sel11_d_priority: assert property (
        @(posedge clk)
        (S == 2'b11 && (D != 4'b0000)) |-> (Y == 1'b0 && Z == 1'b0)
    );

    // For S=11, A selects Y=1 and Z=0 when D is zero.
    check_sel11_a_priority: assert property (
        @(posedge clk)
        (S == 2'b11 && (D == 4'b0000) && (A != 4'b0000)) |-> (Y == 1'b1 && Z == 1'b0)
    );

    // For S=11, B selects Y=0 and Z=1 when D and A are zero.
    check_sel11_b_priority: assert property (
        @(posedge clk)
        (S == 2'b11 && (D == 4'b0000) && (A == 4'b0000) && (B != 4'b0000)) |-> (Y == 1'b0 && Z == 1'b1)
    );

    // For S=11, outputs are 0 when D, A, and B are all zero.
    check_sel11_default_zero: assert property (
        @(posedge clk)
        (S == 2'b11 && (D == 4'b0000) && (A == 4'b0000) && (B == 4'b0000)) |-> (Y == 1'b0 && Z == 1'b0)
    );

endmodule