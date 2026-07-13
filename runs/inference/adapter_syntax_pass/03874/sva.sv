module NAND4AND2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] Z
);

    // Z[0] is the inverted AND of A and B.
    check_z0_is_ab_nand: assert property (
        @(posedge clk) Z[0] == ~(A & B)
    );

    // Z[1] is the inverted AND of C and D.
    check_z1_is_cd_nand: assert property (
        @(posedge clk) Z[1] == ~(C & D)
    );

    // Z[0] and Z[1] are complementary.
    check_outputs_are_complementary: assert property (
        @(posedge clk) Z[0] != Z[1]
    );

    // If both inputs are high, both outputs must be low.
    check_both_inputs_high_drive_outputs_low: assert property (
        @(posedge clk) (A && B && C && D) |-> (Z == 2'b00)
    );

    // If either A or B is low, Z[0] must be high.
    check_ab_low_drives_z0_high: assert property (
        @(posedge clk) (!A || !B) |-> (Z[0] == 1'b1)
    );

    // If either C or D is low, Z[1] must be high.
    check_cd_low_drives_z1_high: assert property (
        @(posedge clk) (!C || !D) |-> (Z[1] == 1'b1)
    );

    // If A and C are high, Z[0] and Z[1] must be low.
    check_ac_high_drives_outputs_low: assert property (
        @(posedge clk) (A && C) |-> (Z == 2'b00)
    );

    // If B and D are high, Z[0] and Z[1] must be low.
    check_bd_high_drives_outputs_low: assert property (
        @(posedge clk) (B && D) |-> (Z == 2'b00)
    );

endmodule