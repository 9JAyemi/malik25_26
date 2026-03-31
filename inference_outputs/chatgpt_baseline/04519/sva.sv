module nor_and_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Supply pins hold their declared constant values.
    check_supply_constants: assert property (
        @(posedge clk) disable iff (1'b0)
        (VPWR == 1'b1) && (VGND == 1'b0) && (VPB == 1'b1) && (VNB == 1'b0)
    );

    // Y matches the implemented NOR-of-NORs logic.
    check_y_boolean_equation: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ((A | B) & (C | D))
    );

    // If both A and B are low, Y must be low.
    check_ab_zero_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A == 1'b0) && (B == 1'b0)) |-> (Y == 1'b0)
    );

    // If both C and D are low, Y must be low.
    check_cd_zero_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((C == 1'b0) && (D == 1'b0)) |-> (Y == 1'b0)
    );

    // A high Y requires at least one of A or B to be high.
    check_y_high_requires_ab_or: assert property (
        @(posedge clk) disable iff (1'b0)
        (Y == 1'b1) |-> ((A == 1'b1) || (B == 1'b1))
    );

    // A high Y requires at least one of C or D to be high.
    check_y_high_requires_cd_or: assert property (
        @(posedge clk) disable iff (1'b0)
        (Y == 1'b1) |-> ((C == 1'b1) || (D == 1'b1))
    );

    // One high input in each pair drives Y high.
    check_pairwise_or_drives_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (((A == 1'b1) || (B == 1'b1)) && ((C == 1'b1) || (D == 1'b1))) |-> (Y == 1'b1)
    );

endmodule