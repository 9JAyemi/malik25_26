module sky130_fd_sc_lp__nor2_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B
);

    // Y always equals the NOR of A and B.
    check_nor_equation: assert property (
        @(posedge clk) (Y === ~(A | B))
    );

    // When both inputs are low, Y is high.
    check_both_low_drive_y_high: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b0)) |-> (Y === 1'b1)
    );

    // A high forces Y low.
    check_a_high_drives_y_low: assert property (
        @(posedge clk) (A === 1'b1) |-> (Y === 1'b0)
    );

    // B high forces Y low.
    check_b_high_drives_y_low: assert property (
        @(posedge clk) (B === 1'b1) |-> (Y === 1'b0)
    );

endmodule