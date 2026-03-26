module sky130_fd_sc_hd__a32oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NAND-AND logic function.
    check_y_function: assert property (
        @(posedge clk) Y === ((~(A1 & A2 & A3)) & (~(B1 & B2)))
    );

    // A1, A2, and A3 all high force Y low.
    check_a_group_forces_low: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> (Y === 1'b0)
    );

    // B1 and B2 both high force Y low.
    check_b_group_forces_low: assert property (
        @(posedge clk) (B1 & B2) |-> (Y === 1'b0)
    );

    // If neither product term is active, Y is high.
    check_no_active_group_drives_high: assert property (
        @(posedge clk) ((~(A1 & A2 & A3)) & (~(B1 & B2))) |-> (Y === 1'b1)
    );

    // Y high implies both product terms are inactive.
    check_y_high_means_no_active_group: assert property (
        @(posedge clk) (Y === 1'b1) |-> ((~(A1 & A2 & A3)) & (~(B1 & B2)))
    );

    // Y low implies at least one product term is active.
    check_y_low_means_active_group: assert property (
        @(posedge clk) (Y === 1'b0) |-> ((A1 & A2 & A3) | (B1 & B2))
    );

endmodule