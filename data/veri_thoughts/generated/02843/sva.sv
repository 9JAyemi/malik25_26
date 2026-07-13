module custom_module_sva (
    input logic clk,    // External sampling clock (DUT has no clock/reset)
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y equals NOR of (A1&A2), (B1&B2), and C1.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~((B1 & B2) | (A1 & A2) | C1)
    );

    // C1 high forces Y low.
    check_C1_dominates_low: assert property (
        @(posedge clk) C1 |-> (Y == 1'b0)
    );

    // A1&A2 high forces Y low.
    check_A_pair_dominates_low: assert property (
        @(posedge clk) (A1 & A2) |-> (Y == 1'b0)
    );

    // B1&B2 high forces Y low.
    check_B_pair_dominates_low: assert property (
        @(posedge clk) (B1 & B2) |-> (Y == 1'b0)
    );

    // If none of the sources are active, Y is high.
    check_no_sources_sets_Y_high: assert property (
        @(posedge clk) (!C1 && !(A1 & A2) && !(B1 & B2)) |-> (Y == 1'b1)
    );

    // Y high implies no source is active.
    check_Y_high_implies_no_sources: assert property (
        @(posedge clk) Y |-> (!C1 && !(A1 & A2) && !(B1 & B2))
    );

    // Y low implies at least one source is active.
    check_Y_low_implies_some_source: assert property (
        @(posedge clk) !Y |-> (C1 || (A1 & A2) || (B1 & B2))
    );

    // A rising C1 immediately forces Y low.
    check_C1_rise_forces_Y_low: assert property (
        @(posedge clk) $rose(C1) |-> (Y == 1'b0)
    );

    // A falling edge on Y implies some source is active now.
    check_Y_fall_implies_source_active: assert property (
        @(posedge clk) $fell(Y) |-> (C1 || (A1 & A2) || (B1 & B2))
    );

    // A rising edge on Y implies all sources inactive now.
    check_Y_rise_implies_no_sources: assert property (
        @(posedge clk) $rose(Y) |-> (!C1 && !(A1 & A2) && !(B1 & B2))
    );

endmodule