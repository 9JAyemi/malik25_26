module bitwise_and_or_sva (
    input logic        clk,
    input logic [7:0]  x,
    input logic [7:0]  y,
    input logic        out
);

    // Out matches the implemented AND/OR reduction tree.
    check_out_matches_tree: assert property (
        @(posedge clk)
        out == ((((x[0] & y[0]) | (x[1] & y[1])) & ((x[2] & y[2]) | (x[3] & y[3])))
             | (((x[4] & y[4]) | (x[5] & y[5])) & ((x[6] & y[6]) | (x[7] & y[7]))))
    );

    // A true first reduction branch must drive out high.
    check_first_branch_drives_out_high: assert property (
        @(posedge clk)
        ((((x[0] & y[0]) | (x[1] & y[1])) & ((x[2] & y[2]) | (x[3] & y[3]))) |-> (out == 1'b1)
    );

    // A true second reduction branch must drive out high.
    check_second_branch_drives_out_high: assert property (
        @(posedge clk)
        ((((x[4] & y[4]) | (x[5] & y[5])) & ((x[6] & y[6]) | (x[7] & y[7]))) |-> (out == 1'b1)
    );

    // A high out must come from one of the two reduction branches.
    check_out_high_has_valid_source: assert property (
        @(posedge clk)
        (out == 1'b1) |-> (((((x[0] & y[0]) | (x[1] & y[1])) & ((x[2] & y[2]) | (x[3] & y[3])))
                         | (((x[4] & y[4]) | (x[5] & y[5])) & ((x[6] & y[6]) | (x[7] & y[7])))) == 1'b1)
    );

    // If neither reduction branch is true, out must be low.
    check_no_active_branch_drives_out_low: assert property (
        @(posedge clk)
        (!((((x[0] & y[0]) | (x[1] & y[1])) & ((x[2] & y[2]) | (x[3] & y[3])))) &&
         !((((x[4] & y[4]) | (x[5] & y[5])) & ((x[6] & y[6]) | (x[7] & y[7]))))) |-> (out == 1'b0)
    );

    // The first branch needs both of its OR groups when the second branch is inactive.
    check_first_branch_requires_both_or_groups: assert property (
        @(posedge clk)
        ((((x[0] & y[0]) | (x[1] & y[1])) ^ ((x[2] & y[2]) | (x[3] & y[3]))) &&
         !((((x[4] & y[4]) | (x[5] & y[5])) & ((x[6] & y[6]) | (x[7] & y[7]))))) |-> (out == 1'b0)
    );

    // The second branch needs both of its OR groups when the first branch is inactive.
    check_second_branch_requires_both_or_groups: assert property (
        @(posedge clk)
        ((((x[4] & y[4]) | (x[5] & y[5])) ^ ((x[6] & y[6]) | (x[7] & y[7]))) &&
         !((((x[0] & y[0]) | (x[1] & y[1])) & ((x[2] & y[2]) | (x[3] & y[3]))))) |-> (out == 1'b0)
    );

    // A zero x input forces all pairwise AND terms low.
    check_zero_x_forces_out_low: assert property (
        @(posedge clk)
        (x == 8'h00) |-> (out == 1'b0)
    );

    // A zero y input forces all pairwise AND terms low.
    check_zero_y_forces_out_low: assert property (
        @(posedge clk)
        (y == 8'h00) |-> (out == 1'b0)
    );

endmodule