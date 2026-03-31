module sky130_fd_sc_hd__o21bai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Sample combinational behavior on an external clock; the RTL has no reset.

    // Y matches the implemented O21BAI gate equation.
    check_output_matches_gate_equation: assert property (
        @(posedge clk) disable iff (1'b0) Y == ~((~B1_N) & (A1 | A2))
    );

    // B1_N high forces the output high.
    check_b1n_high_forces_y_high: assert property (
        @(posedge clk) disable iff (1'b0) B1_N |-> Y
    );

    // Both A inputs low force the output high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) disable iff (1'b0) (!A1 && !A2) |-> Y
    );

    // A1 high with active-low B input forces the output low.
    check_a1_high_and_b1n_low_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0) (!B1_N && A1) |-> !Y
    );

    // A2 high with active-low B input forces the output low.
    check_a2_high_and_b1n_low_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0) (!B1_N && A2) |-> !Y
    );

    // A low output requires B1_N to be low.
    check_y_low_requires_b1n_low: assert property (
        @(posedge clk) disable iff (1'b0) !Y |-> !B1_N
    );

    // A low output requires at least one A input high.
    check_y_low_requires_a_input_high: assert property (
        @(posedge clk) disable iff (1'b0) !Y |-> (A1 | A2)
    );

    // With B1_N low, a high output requires both A inputs low.
    check_y_high_with_b1n_low_requires_a_inputs_low: assert property (
        @(posedge clk) disable iff (1'b0) (Y && !B1_N) |-> (!A1 && !A2)
    );

endmodule