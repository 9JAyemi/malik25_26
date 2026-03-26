module sky130_fd_sc_lp__o21ba_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Sampling clock only; the RTL has no clock or reset.
    // DUT is combinational: X = ~(B1_N | ~(A1 | A2)).

    // X must match the implemented boolean function.
    check_output_function: assert property (
        @(posedge clk) X == (~(B1_N | ~(A1 | A2)))
    );

    // A high B1_N forces the second NOR output low.
    check_b1n_high_forces_x_low: assert property (
        @(posedge clk) B1_N |-> !X
    );

    // Both A inputs low force the first NOR high and X low.
    check_a_inputs_low_force_x_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> !X
    );

    // A1 can drive X high when B1_N is low.
    check_a1_high_with_b1n_low_drives_x_high: assert property (
        @(posedge clk) (!B1_N && A1) |-> X
    );

    // A2 can drive X high when B1_N is low.
    check_a2_high_with_b1n_low_drives_x_high: assert property (
        @(posedge clk) (!B1_N && A2) |-> X
    );

endmodule