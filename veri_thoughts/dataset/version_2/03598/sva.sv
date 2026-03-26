module sky130_fd_sc_ls__a41oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // Y matches the implemented combinational equation.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ((A1 && A2) || (A3 && A4) || B1)
    );

    // B1 high is sufficient to drive Y high.
    check_b1_drives_y_high: assert property (
        @(posedge clk) B1 |-> Y
    );

    // A1 and A2 high together are sufficient to drive Y high.
    check_a1_a2_drive_y_high: assert property (
        @(posedge clk) (A1 && A2) |-> Y
    );

    // A3 and A4 high together are sufficient to drive Y high.
    check_a3_a4_drive_y_high: assert property (
        @(posedge clk) (A3 && A4) |-> Y
    );

    // Y low means all three OR terms are low.
    check_y_low_requires_all_terms_low: assert property (
        @(posedge clk) !Y |-> (!(A1 && A2) && !(A3 && A4) && !B1)
    );

endmodule