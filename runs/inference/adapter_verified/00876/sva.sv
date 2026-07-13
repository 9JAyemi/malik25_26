module three_to_one_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y
);

// Y must match the RTL equation.
    check_function_equation: assert property (
        @(posedge clk) Y == ((A1 & A2) | B1)
    );

// B1 high must force Y high.
    check_b1_forces_y_high: assert property (
        @(posedge clk) B1 |-> Y
    );

// A1 and A2 high together must force Y high.
    check_a1_a2_force_y_high: assert property (
        @(posedge clk) (A1 & A2) |-> Y
    );

// With B1 low, Y must follow A1 & A2.
    check_b1_low_passes_a1_a2: assert property (
        @(posedge clk) !B1 |-> (Y == (A1 & A2))
    );

// With B1 low and A1 low, Y must be low.
    check_b1_low_a1_low_gives_y_low: assert property (
        @(posedge clk) (!B1 && !A1) |-> !Y
    );

// With B1 low and A2 low, Y must be low.
    check_b1_low_a2_low_gives_y_low: assert property (
        @(posedge clk) (!B1 && !A2) |-> !Y
    );

// A high Y must come from B1 or A1 & A2.
    check_y_high_has_valid_source: assert property (
        @(posedge clk) Y |-> (B1 || (A1 && A2))
    );

endmodule
