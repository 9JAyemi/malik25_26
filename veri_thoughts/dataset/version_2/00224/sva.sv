module sky130_fd_sc_lp__a211oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented A211OI Boolean function.
    check_boolean_function: assert property (
        @(posedge clk) Y == ~((A1 & A2) | B1 | C1)
    );

    // Any high on B1 or C1 forces the NOR output low.
    check_b1_or_c1_force_low: assert property (
        @(posedge clk) (B1 == 1'b1 || C1 == 1'b1) |-> (Y == 1'b0)
    );

    // A1 and A2 high together force the output low.
    check_a1_a2_and_force_low: assert property (
        @(posedge clk) (A1 == 1'b1 && A2 == 1'b1) |-> (Y == 1'b0)
    );

    // Y high requires B1 and C1 low and the A1/A2 AND term low.
    check_high_output_conditions: assert property (
        @(posedge clk) (Y == 1'b1) |-> (B1 == 1'b0 && C1 == 1'b0 && !(A1 == 1'b1 && A2 == 1'b1))
    );

    // With B1 and C1 low, a low on either A1 or A2 makes Y high.
    check_missing_and_term_drives_high: assert property (
        @(posedge clk) (B1 == 1'b0 && C1 == 1'b0 && (A1 == 1'b0 || A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // If Y is low while B1 and C1 are low, both A1 and A2 must be high.
    check_low_output_from_and_term_only: assert property (
        @(posedge clk) (Y == 1'b0 && B1 == 1'b0 && C1 == 1'b0) |-> (A1 == 1'b1 && A2 == 1'b1)
    );

endmodule