module sky130_fd_sc_ls__o21bai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented combinational function.
    check_y_function: assert property (
        @(posedge clk) Y == ~(~B1_N & (A1 | A2))
    );

    // A high B1_N forces Y high.
    check_b1n_high_forces_y_high: assert property (
        @(posedge clk) B1_N |-> Y
    );

    // Both A inputs low force Y high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) (!A1 && !A2) |-> Y
    );

    // With B1_N low, any high A input forces Y low.
    check_or_term_with_b1n_low_forces_y_low: assert property (
        @(posedge clk) (!B1_N && (A1 || A2)) |-> !Y
    );

    // A low output requires B1_N low and the OR term high.
    check_y_low_only_when_expected: assert property (
        @(posedge clk) (!Y) |-> (!B1_N && (A1 || A2))
    );

endmodule