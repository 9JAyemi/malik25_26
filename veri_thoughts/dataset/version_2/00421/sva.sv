module sky130_fd_sc_ls__a211oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented A211OI logic.
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ~((A1 & A2) | B1 | C1)
    );

    // B1 high forces the NOR output low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        B1 |-> !Y
    );

    // C1 high forces the NOR output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        C1 |-> !Y
    );

    // A1 and A2 high together force the NOR output low.
    check_a1_a2_force_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 && A2) |-> !Y
    );

    // Y high means all NOR inputs are inactive.
    check_y_high_requires_all_nor_inputs_low: assert property (
        @(posedge clk) disable iff (1'b0)
        Y |-> (!B1 && !C1 && !(A1 && A2))
    );

    // If all NOR inputs are low, Y must be high.
    check_all_nor_inputs_low_gives_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (!B1 && !C1 && !(A1 && A2)) |-> Y
    );

    // Stable inputs keep the combinational output stable.
    check_stable_inputs_keep_y_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        $stable({A1, A2, B1, C1}) |-> $stable(Y)
    );

endmodule