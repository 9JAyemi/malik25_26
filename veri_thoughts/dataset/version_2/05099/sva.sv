module and_nor_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented gate equation.
    check_y_matches_gate_equation: assert property (
        @(posedge clk) Y == ~(~B1_N | (A1 & A2))
    );

    // Low B1_N forces Y low.
    check_b1_n_low_forces_y_low: assert property (
        @(posedge clk) !B1_N |-> !Y
    );

    // A1 and A2 high together force Y low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // High B1_N with low A1 makes Y high.
    check_b1_n_high_a1_low_drives_y_high: assert property (
        @(posedge clk) (B1_N && !A1) |-> Y
    );

    // High B1_N with low A2 makes Y high.
    check_b1_n_high_a2_low_drives_y_high: assert property (
        @(posedge clk) (B1_N && !A2) |-> Y
    );

    // Y high requires B1_N high.
    check_y_high_requires_b1_n_high: assert property (
        @(posedge clk) Y |-> B1_N
    );

    // Y high means A1 and A2 are not both high.
    check_y_high_requires_not_a1_a2_high: assert property (
        @(posedge clk) Y |-> !(A1 && A2)
    );

    // Low Y with high B1_N requires both A inputs high.
    check_y_low_with_b1_n_high_requires_a1_a2_high: assert property (
        @(posedge clk) (!Y && B1_N) |-> (A1 && A2)
    );

endmodule