module nand4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y matches the implemented nand-of-nands logic.
    check_nand4_function: assert property (
        @(posedge clk) Y == ~((~(A & B)) & (~(C & D)))
    );

    // A and B both high force Y high.
    check_ab_pair_sets_y_high: assert property (
        @(posedge clk) (A & B) |-> Y
    );

    // C and D both high force Y high.
    check_cd_pair_sets_y_high: assert property (
        @(posedge clk) (C & D) |-> Y
    );

    // If neither pair is high, Y must be low.
    check_no_active_pair_sets_y_low: assert property (
        @(posedge clk) (!(A & B) && !(C & D)) |-> !Y
    );

    // All inputs low produce a low Y.
    check_all_inputs_low: assert property (
        @(posedge clk) (!A && !B && !C && !D) |-> !Y
    );

    // All inputs high produce a high Y.
    check_all_inputs_high: assert property (
        @(posedge clk) (A && B && C && D) |-> Y
    );

endmodule