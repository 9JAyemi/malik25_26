module main_sva(
    input logic clk,
    input logic [2:0] A1,
    input logic [2:0] A2,
    input logic [2:0] A3,
    input logic Y
);

    // Y matches the OR of the three reduction-AND terms.
    check_y_definition: assert property (
        @(posedge clk) Y == ((&A1) | (&A2) | (&A3))
    );

    // A1 being all ones forces Y high.
    check_a1_all_ones_sets_y: assert property (
        @(posedge clk) (&A1) |-> Y
    );

    // A2 being all ones forces Y high.
    check_a2_all_ones_sets_y: assert property (
        @(posedge clk) (&A2) |-> Y
    );

    // A3 being all ones forces Y high.
    check_a3_all_ones_sets_y: assert property (
        @(posedge clk) (&A3) |-> Y
    );

    // If no input bus is all ones, Y must be low.
    check_no_full_bus_means_y_low: assert property (
        @(posedge clk) (!(&A1) && !(&A2) && !(&A3)) |-> !Y
    );

    // A high Y requires at least one bus to be all ones.
    check_y_high_requires_full_bus: assert property (
        @(posedge clk) Y |-> ((&A1) || (&A2) || (&A3))
    );

    // A low Y means A1 is not all ones.
    check_y_low_excludes_a1_full: assert property (
        @(posedge clk) !Y |-> !(&A1)
    );

    // A low Y means A2 is not all ones.
    check_y_low_excludes_a2_full: assert property (
        @(posedge clk) !Y |-> !(&A2)
    );

    // A low Y means A3 is not all ones.
    check_y_low_excludes_a3_full: assert property (
        @(posedge clk) !Y |-> !(&A3)
    );

endmodule