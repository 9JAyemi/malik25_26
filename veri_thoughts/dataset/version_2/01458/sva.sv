module sky130_fd_sc_ls__o22a_sva (
    input logic CLK,
    input logic RESETn,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // Output equals (A1|A2) & (B1|B2).
    check_functional_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn) X == ((A1 | A2) & (B1 | B2))
    );

    // If X is HIGH, at least one A and one B input are HIGH.
    check_x_high_requires_groups_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (X == 1'b1) |-> ((A1 | A2) && (B1 | B2))
    );

    // If both OR-groups are HIGH, X must be HIGH.
    check_groups_high_implies_x_high: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1 | A2) && (B1 | B2)) |-> (X == 1'b1)
    );

    // If neither A1 nor A2 is HIGH, X must be LOW.
    check_a_group_zero_implies_x_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (~(A1 | A2)) |-> (X == 1'b0)
    );

    // If neither B1 nor B2 is HIGH, X must be LOW.
    check_b_group_zero_implies_x_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (~(B1 | B2)) |-> (X == 1'b0)
    );

    // If X is LOW, then not both OR-groups are HIGH.
    check_x_low_implies_not_both_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (X == 1'b0) |-> ~((A1 | A2) && (B1 | B2))
    );

    // When B-group is HIGH, X mirrors (A1|A2).
    check_b_group_high_x_follows_a_group: assert property (
        @(posedge CLK) disable iff (!RESETn) ((B1 | B2) == 1'b1) |-> (X == (A1 | A2))
    );

    // When A-group is HIGH, X mirrors (B1|B2).
    check_a_group_high_x_follows_b_group: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1 | A2) == 1'b1) |-> (X == (B1 | B2))
    );
endmodule