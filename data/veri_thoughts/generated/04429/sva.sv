module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y matches the implemented combinational equation.
    check_y_equation: assert property (
        @(posedge clk) Y == ((~A1 | ~A2 | ~A3) & B1)
    );

    // Y must be low whenever B1 is low.
    check_y_low_when_b1_low: assert property (
        @(posedge clk) !B1 |-> !Y
    );

    // Y must be low when all A inputs are high.
    check_y_low_when_all_a_high: assert property (
        @(posedge clk) (A1 && A2 && A3) |-> !Y
    );

    // Y must be high when B1 is high and any A input is low.
    check_y_high_when_b1_high_and_any_a_low: assert property (
        @(posedge clk) (B1 && (!A1 || !A2 || !A3)) |-> Y
    );

    // A high Y requires B1 to be high.
    check_y_implies_b1_high: assert property (
        @(posedge clk) Y |-> B1
    );

    // A high Y requires at least one A input to be low.
    check_y_implies_any_a_low: assert property (
        @(posedge clk) Y |-> (!A1 || !A2 || !A3)
    );

endmodule