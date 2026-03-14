module and4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic clk,
    input logic rst
);
    ///// Reset behavior /////
    // While reset is asserted low, X must be 0.
    check_reset_forces_x_low: assert property (
        @(posedge clk) (rst == 1'b0) |-> (X == 1'b0)
    );

    // On the cycle reset deasserts (low->high), X remains 0 (register updates after this edge).
    check_zero_on_reset_release_cycle: assert property (
        @(posedge clk) $rose(rst) |-> (X == 1'b0)
    );

    ///// Registered 4-input AND behavior /////
    // When out of reset for two cycles, X equals previous cycle's A&B&C&D.
    check_registered_and_equivalence: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (X == $past(A & B & C & D))
    );

    // If all inputs are 1 in this cycle, X will be 1 next cycle (out of reset).
    check_all_ones_implies_x1_next: assert property (
        @(posedge clk) disable iff (!rst) (A & B & C & D) |=> (X == 1'b1)
    );

    // If any input is 0 in this cycle, X will be 0 next cycle (out of reset).
    check_any_zero_implies_x0_next: assert property (
        @(posedge clk) disable iff (!rst) !(A & B & C & D) |=> (X == 1'b0)
    );

    // After a reset assertion (high->low), X is 0 on the following cycle.
    check_zero_after_reset_assertion_next: assert property (
        @(posedge clk) $fell(rst) |=> (X == 1'b0)
    );
endmodule