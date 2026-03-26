module sky130_fd_sc_hd__nand3b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C
);

    // Y matches the implemented NAND-with-inverted-A function.
    check_function_equation: assert property (
        @(posedge clk) Y == ~(B & ~A_N & C)
    );

    // A_N high forces the inverted A input low, so Y must be high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> (Y == 1'b1)
    );

    // B low disables the NAND term, so Y must be high.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) !B |-> (Y == 1'b1)
    );

    // C low disables the NAND term, so Y must be high.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) !C |-> (Y == 1'b1)
    );

    // Y is low only when A_N is low and both B and C are high.
    check_all_active_drives_y_low: assert property (
        @(posedge clk) (!A_N && B && C) |-> (Y == 1'b0)
    );

    // A low output requires all effective NAND inputs to be active.
    check_y_low_requires_all_active: assert property (
        @(posedge clk) (Y == 1'b0) |-> (!A_N && B && C)
    );

endmodule