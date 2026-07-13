module sky130_fd_sc_ls__o211a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X must implement ((A1 | A2) & B1 & C1).
    check_output_function: assert property (
        @(posedge clk) X === (((A1 | A2) & B1) & C1)
    );

    // X high requires B1 high.
    check_x_high_requires_b1: assert property (
        @(posedge clk) X |-> B1
    );

    // X high requires C1 high.
    check_x_high_requires_c1: assert property (
        @(posedge clk) X |-> C1
    );

    // X high requires at least one of A1 or A2 high.
    check_x_high_requires_or_input: assert property (
        @(posedge clk) X |-> (A1 | A2)
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // C1 low forces X low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

    // Both OR inputs low force X low.
    check_or_inputs_low_force_x_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> !X
    );

    // A1 with B1 and C1 high drives X high.
    check_a1_path_drives_x: assert property (
        @(posedge clk) (A1 && B1 && C1) |-> X
    );

    // A2 with B1 and C1 high drives X high.
    check_a2_path_drives_x: assert property (
        @(posedge clk) (A2 && B1 && C1) |-> X
    );

endmodule