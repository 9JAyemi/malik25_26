module sky130_fd_sc_hs__nand4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic Y
);

    // Y matches the implemented two-stage NAND expression.
    check_y_matches_implemented_logic: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ~(~(A & B) & ~(C & D))
    );

    // A and B both high force Y high.
    check_ab_pair_forces_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (A & B) |-> Y
    );

    // C and D both high force Y high.
    check_cd_pair_forces_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (C & D) |-> Y
    );

    // If neither input pair is fully high, Y is low.
    check_no_active_pair_forces_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (!(A & B) && !(C & D)) |-> !Y
    );

    // Y can only be high when at least one input pair is fully high.
    check_y_high_requires_active_pair: assert property (
        @(posedge clk) disable iff (1'b0)
        Y |-> ((A & B) || (C & D))
    );

endmodule