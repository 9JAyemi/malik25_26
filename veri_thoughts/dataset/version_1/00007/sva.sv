module nor4b_4_input_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

    // Y must always equal the NOR of A, B, C, and D_N.
    check_nor_equation: assert property (
        @(posedge clk) Y == ~(A | B | C | D_N)
    );

    // If all inputs are low, Y must be high.
    check_all_low_drives_high: assert property (
        @(posedge clk) (!A && !B && !C && !D_N) |-> (Y == 1'b1)
    );

    // A high forces Y low.
    check_a_high_drives_low: assert property (
        @(posedge clk) A |-> (Y == 1'b0)
    );

    // B high forces Y low.
    check_b_high_drives_low: assert property (
        @(posedge clk) B |-> (Y == 1'b0)
    );

    // C high forces Y low.
    check_c_high_drives_low: assert property (
        @(posedge clk) C |-> (Y == 1'b0)
    );

    // D_N high forces Y low.
    check_d_n_high_drives_low: assert property (
        @(posedge clk) D_N |-> (Y == 1'b0)
    );

    // A high Y means all inputs are low.
    check_high_output_requires_all_low: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!A && !B && !C && !D_N)
    );

    // A low Y means at least one input is high.
    check_low_output_requires_some_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (A || B || C || D_N)
    );

endmodule