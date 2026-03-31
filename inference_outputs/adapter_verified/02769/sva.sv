module sky130_fd_sc_ms__a221oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

// Y matches the implemented NOR-of-ANDs function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~((B1 & B2) | C1 | (A1 & A2))
    );

// C1 high forces Y low.
    check_c1_forces_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

// A1 and A2 high together force Y low.
    check_a_pair_forces_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

// B1 and B2 high together force Y low.
    check_b_pair_forces_low: assert property (
        @(posedge clk) (B1 && B2) |-> !Y
    );

// With no asserted NOR inputs, Y must be high.
    check_no_active_input_sets_high: assert property (
        @(posedge clk) (!C1 && !(A1 && A2) && !(B1 && B2)) |-> Y
    );

// A high Y requires all NOR inputs to be inactive.
    check_high_output_requires_all_inputs_inactive: assert property (
        @(posedge clk) Y |-> (!C1 && !(A1 && A2) && !(B1 && B2))
    );

endmodule
