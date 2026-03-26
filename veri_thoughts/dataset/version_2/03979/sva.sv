module sky130_fd_sc_ls__a31o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // No reset in RTL; sample the combinational function on clk.

    // X must equal B1 OR (A1 AND A2 AND A3).
    check_function_exact: assert property (
        @(posedge clk) X == (B1 | (A1 & A2 & A3))
    );

    // B1 high must force X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // With B1 low, X must match the 3-input AND term.
    check_and_path_when_b1_low: assert property (
        @(posedge clk) !B1 |-> (X == (A1 & A2 & A3))
    );

    // All three A inputs high must force X high.
    check_all_a_high_forces_x_high: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> X
    );

    // X low implies B1 is low and at least one A input is low.
    check_x_low_condition: assert property (
        @(posedge clk) !X |-> (!B1 && (!A1 || !A2 || !A3))
    );

endmodule