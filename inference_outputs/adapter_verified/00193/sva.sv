module sky130_fd_sc_hd__a221oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

// Y matches the implemented NOR-of-ANDs function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((B1 & B2) | C1 | (A1 & A2))
    );

// C1 high forces Y low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

// A1 and A2 high together force Y low.
    check_a_pair_forces_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

// B1 and B2 high together force Y low.
    check_b_pair_forces_y_low: assert property (
        @(posedge clk) (B1 && B2) |-> !Y
    );

// With no asserted NOR input, Y must be high.
    check_no_active_input_sets_y_high: assert property (
        @(posedge clk) (!C1 && !(A1 && A2) && !(B1 && B2)) |-> Y
    );

// A high Y requires C1, A1&A2, or B1&B2 to be low.
    check_y_high_requires_some_input_low: assert property (
        @(posedge clk) Y |-> (!C1 && !(A1 && A2) && !(B1 && B2))
    );

endmodule
