module sky130_fd_sc_hd__a221oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y implements the AOI221 combinational equation.
    check_function_equation: assert property (
        @(posedge clk) Y == ~((B1 & B2) | C1 | (A1 & A2))
    );

    // C1 high forces the output low.
    check_c1_forces_output_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // A1 and A2 high together force the output low.
    check_a_and_pair_forces_output_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // B1 and B2 high together force the output low.
    check_b_and_pair_forces_output_low: assert property (
        @(posedge clk) (B1 && B2) |-> !Y
    );

    // All three NOR inputs low drive the output high.
    check_all_nor_inputs_low_drive_output_high: assert property (
        @(posedge clk) (!C1 && !(A1 && A2) && !(B1 && B2)) |-> Y
    );

    // A high output requires all three NOR inputs to be low.
    check_output_high_requires_all_nor_inputs_low: assert property (
        @(posedge clk) Y |-> (!C1 && !(A1 && A2) && !(B1 && B2))
    );

    // A low output requires at least one NOR input to be high.
    check_output_low_requires_any_nor_input_high: assert property (
        @(posedge clk) !Y |-> (C1 || (A1 && A2) || (B1 && B2))
    );

endmodule