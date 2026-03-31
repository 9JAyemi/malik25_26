module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

// Y matches the implemented NOR-of-ANDs function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((A1 & A2 & B1) | (A1 & B1))
    );

// A high B1 forces Y low.
    check_b1_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// A high A1 and A2 force Y low.
    check_a1_a2_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

// With B1 low, Y is the inverse of A1.
    check_y_inverts_a1_when_b1_low: assert property (
        @(posedge clk) !B1 |-> (Y == ~A1)
    );

// With A1 low, Y is the inverse of A2.
    check_y_inverts_a2_when_a1_low: assert property (
        @(posedge clk) !A1 |-> (Y == ~A2)
    );

// With A2 low, Y is the inverse of A1.
    check_y_inverts_a1_when_a2_low: assert property (
        @(posedge clk) !A2 |-> (Y == ~A1)
    );

// With A1 and A2 low, Y is high.
    check_y_high_when_a1_a2_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> Y
    );

// With A1 and B1 low, Y is high.
    check_y_high_when_a1_b1_low: assert property (
        @(posedge clk) (!A1 && !B1) |-> Y
    );

// With A2 and B1 low, Y is high.
    check_y_high_when_a2_b1_low: assert property (
        @(posedge clk) (!A2 && !B1) |-> Y
    );

endmodule
