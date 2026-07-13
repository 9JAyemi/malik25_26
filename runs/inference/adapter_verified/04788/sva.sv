module sky130_fd_sc_lp__o31ai_sva (
    input logic clk,
    input logic Y,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

// Y matches the implemented OR-then-NAND function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~(B1 & (A1 | A2 | A3))
    );

// A high B1 forces Y low.
    check_b1_forces_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// Any high A input forces Y low.
    check_any_a_high_forces_low: assert property (
        @(posedge clk) (A1 | A2 | A3) |-> !Y
    );

// With B1 low, Y is high-impedance.
    check_b1_low_high_impedance: assert property (
        @(posedge clk) !B1 |-> (Y == 1'bz)
    );

// With all A inputs low, Y is high.
    check_all_a_low_high: assert property (
        @(posedge clk) !(A1 | A2 | A3) |-> Y
    );

// With B1 low and any A input high, Y is high.
    check_b1_low_any_a_high_high: assert property (
        @(posedge clk) (!B1 && (A1 | A2 | A3)) |-> Y
    );

endmodule
