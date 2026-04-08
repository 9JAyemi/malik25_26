module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y matches the gate-level structure in the RTL.
    check_y_matches_structure: assert property (
        @(posedge clk) Y == ~((~(A2 & A1)) & (~(B2 & B1)))
    );

    // Y simplifies to the OR of the two input pairs.
    check_y_matches_simplified_function: assert property (
        @(posedge clk) Y == ((A1 & A2) | (B1 & B2))
    );

    // A1 and A2 both high force Y high.
    check_a_pair_drives_y_high: assert property (
        @(posedge clk) (A1 & A2) |-> Y
    );

    // B1 and B2 both high force Y high.
    check_b_pair_drives_y_high: assert property (
        @(posedge clk) (B1 & B2) |-> Y
    );

    // If neither pair is fully high, Y must be low.
    check_no_complete_pair_drives_y_low: assert property (
        @(posedge clk) (!(A1 & A2) && !(B1 & B2)) |-> !Y
    );

    // A low Y means neither input pair is fully high.
    check_y_low_implies_no_complete_pair: assert property (
        @(posedge clk) !Y |-> (!(A1 & A2) && !(B1 & B2))
    );

endmodule