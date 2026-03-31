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

    // Y matches the implemented NOR-NOR function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ~((~(A | B)) & (~(C | D)))
    );

    // A and B high force Y low.
    check_ab_pair_forces_low: assert property (
        @(posedge clk) (A & B) |-> !Y
    );

    // C and D high force Y low.
    check_cd_pair_forces_low: assert property (
        @(posedge clk) (C & D) |-> !Y
    );

    // A and C high force Y low.
    check_ac_pair_forces_low: assert property (
        @(posedge clk) (A & C) |-> !Y
    );

    // A and D high force Y low.
    check_ad_pair_forces_low: assert property (
        @(posedge clk) (A & D) |-> !Y
    );

    // B and C high force Y low.
    check_bc_pair_forces_low: assert property (
        @(posedge clk) (B & C) |-> !Y
    );

    // B and D high force Y low.
    check_bd_pair_forces_low: assert property (
        @(posedge clk) (B & D) |-> !Y
    );

    // All inputs low force Y high.
    check_all_inputs_low_forces_high: assert property (
        @(posedge clk) (!A & !B & !C & !D) |-> Y
    );

    // All inputs high force Y low.
    check_all_inputs_high_forces_low: assert property (
        @(posedge clk) (A & B & C & D) |-> !Y
    );

    // Y low implies at least one input pair is high.
    check_y_low_has_high_pair: assert property (
        @(posedge clk) !Y |-> ((A & B) || (C & D) || (A & C) || (A & D) || (B & C) || (B & D))
    );

endmodule