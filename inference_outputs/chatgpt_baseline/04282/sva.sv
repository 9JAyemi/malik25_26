module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // No clock or reset exists in the RTL; sample combinational behavior on clk.

    // Y matches the implemented NOR-of-ANDs function.
    check_overall_function: assert property (
        @(posedge clk) Y == ~((A1 & A2 & B1) | (A1 & B1))
    );

    // Input combination 000 drives Y high.
    check_truth_table_000: assert property (
        @(posedge clk) (!A1 && !A2 && !B1) |-> (Y == 1'b1)
    );

    // Input combination 001 drives Y high.
    check_truth_table_001: assert property (
        @(posedge clk) (!A1 && !A2 && B1) |-> (Y == 1'b1)
    );

    // Input combination 010 drives Y high.
    check_truth_table_010: assert property (
        @(posedge clk) (!A1 && A2 && !B1) |-> (Y == 1'b1)
    );

    // Input combination 011 drives Y high.
    check_truth_table_011: assert property (
        @(posedge clk) (!A1 && A2 && B1) |-> (Y == 1'b1)
    );

    // Input combination 100 drives Y high.
    check_truth_table_100: assert property (
        @(posedge clk) (A1 && !A2 && !B1) |-> (Y == 1'b1)
    );

    // Input combination 101 drives Y low.
    check_truth_table_101: assert property (
        @(posedge clk) (A1 && !A2 && B1) |-> (Y == 1'b0)
    );

    // Input combination 110 drives Y high.
    check_truth_table_110: assert property (
        @(posedge clk) (A1 && A2 && !B1) |-> (Y == 1'b1)
    );

    // Input combination 111 drives Y low.
    check_truth_table_111: assert property (
        @(posedge clk) (A1 && A2 && B1) |-> (Y == 1'b0)
    );

endmodule