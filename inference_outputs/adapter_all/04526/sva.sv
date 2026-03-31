module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented OR-AND-NOT function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1 & C1)
    );

    // If B1 is low, the AND term is low and Y must be high.
    check_y_high_when_b1_low: assert property (
        @(posedge clk) !B1 |-> Y
    );

    // If C1 is low, the AND term is low and Y must be high.
    check_y_high_when_c1_low: assert property (
        @(posedge clk) !C1 |-> Y
    );

    // If both A inputs are low, the OR term is low and Y must be high.
    check_y_high_when_a_inputs_low: assert property (
        @(posedge clk) !(A1 | A2) |-> Y
    );

    // If B1, C1, and at least one A input are high, Y must be low.
    check_y_low_when_all_active: assert property (
        @(posedge clk) (B1 & C1 & (A1 | A2)) |-> !Y
    );

    // A low Y requires B1, C1, and at least one A input to be high.
    check_y_low_implies_all_active: assert property (
        @(posedge clk) !Y |-> (B1 & C1 & (A1 | A2))
    );

endmodule