module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y matches the implemented NOR-of-AND function.
    check_y_function: assert property (
        @(posedge clk) Y == ~(B1 | (A1 & A2))
    );

    // A high B1 forces the NOR output low.
    check_b1_high_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // A high A1/A2 product term forces the NOR output low.
    check_and_term_high_forces_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // Y is high when both inputs to the NOR are low.
    check_both_nor_inputs_low_gives_y_high: assert property (
        @(posedge clk) (!B1 && !(A1 && A2)) |-> Y
    );

    // A high Y implies B1 is low.
    check_y_high_implies_b1_low: assert property (
        @(posedge clk) Y |-> !B1
    );

    // With B1 low, a low Y implies the AND term is high.
    check_b1_low_and_y_low_implies_and_term_high: assert property (
        @(posedge clk) (!B1 && !Y) |-> (A1 && A2)
    );

endmodule