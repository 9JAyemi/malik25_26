module sky130_fd_sc_hd__a211oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

// Y matches the implemented A211OI logic.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~(A1 & A2 | B1 | C1)
    );

// A high B1 forces Y low.
    check_b1_forces_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// A high C1 forces Y low.
    check_c1_forces_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

// A1 and A2 high together force Y low.
    check_a1_a2_force_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

// With no asserted NOR inputs, Y must be high.
    check_no_nor_inputs_drive_high: assert property (
        @(posedge clk) (!B1 && !C1 && !(A1 && A2)) |-> Y
    );

// A high Y requires all NOR inputs to be inactive.
    check_high_output_requires_no_nor_inputs: assert property (
        @(posedge clk) Y |-> (!B1 && !C1 && !(A1 && A2))
    );

endmodule
