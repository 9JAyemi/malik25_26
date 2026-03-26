module logic_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y must match the implemented gate equation.
    check_output_equation: assert property (
        @(posedge clk) Y == ((~(A1 & A2 & A3)) & (~(B1 & B2)))
    );

    // All three A inputs high must force Y low.
    check_a_triplet_forces_y_low: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> (Y == 1'b0)
    );

    // Both B inputs high must force Y low.
    check_b_pair_forces_y_low: assert property (
        @(posedge clk) (B1 & B2) |-> (Y == 1'b0)
    );

    // If neither NAND input group is fully high, Y must be high.
    check_nonblocking_inputs_drive_y_high: assert property (
        @(posedge clk) ((!(A1 & A2 & A3)) && (!(B1 & B2))) |-> (Y == 1'b1)
    );

    // A high Y means the A-side NAND condition is not blocked.
    check_y_high_requires_not_all_a_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!(A1 & A2 & A3))
    );

    // A high Y means the B-side NAND condition is not blocked.
    check_y_high_requires_not_all_b_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!(B1 & B2))
    );

endmodule