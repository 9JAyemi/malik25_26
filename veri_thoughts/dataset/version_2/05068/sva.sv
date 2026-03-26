module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No RTL clock or reset is present; use the formal global clock.

    // Y must match the implemented OR-of-terms function.
    check_y_matches_function: assert property (
        @($global_clock) Y == ((A1 & A2) | (B1 & B2) | C1)
    );

    // If the A1/A2 term is asserted, Y must be high.
    check_y_high_from_a_pair: assert property (
        @($global_clock) (A1 & A2) |-> (Y == 1'b1)
    );

    // If the B1/B2 term is asserted, Y must be high.
    check_y_high_from_b_pair: assert property (
        @($global_clock) (B1 & B2) |-> (Y == 1'b1)
    );

    // If C1 is asserted, Y must be high.
    check_y_high_from_c1: assert property (
        @($global_clock) C1 |-> (Y == 1'b1)
    );

    // If no input term is asserted, Y must be low.
    check_y_low_when_no_term_set: assert property (
        @($global_clock) !((A1 & A2) | (B1 & B2) | C1) |-> (Y == 1'b0)
    );

    // A high Y must be caused by at least one asserted input term.
    check_y_high_only_with_valid_term: assert property (
        @($global_clock) Y |-> ((A1 & A2) | (B1 & B2) | C1)
    );

endmodule