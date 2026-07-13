module sky130_fd_sc_lp__a2111oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Y matches the implemented A2111OI Boolean equation.
    check_y_equation: assert property (
        @(posedge clk) Y == ~(B1 | C1 | D1 | (A1 & A2))
    );

    // B1 high forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // C1 high forces the NOR output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // D1 high forces the NOR output low.
    check_d1_forces_y_low: assert property (
        @(posedge clk) D1 |-> !Y
    );

    // A1 and A2 high together force the NOR output low.
    check_a1_a2_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // Y is high when all NOR inputs are low.
    check_all_nor_inputs_low_force_y_high: assert property (
        @(posedge clk) (!B1 && !C1 && !D1 && !(A1 && A2)) |-> Y
    );

endmodule