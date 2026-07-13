module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // Y matches the implemented combinational function.
    check_y_functional_equivalence: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ((A1 & A2 & ~A3) | (B1 & ~C1) | (~C1 & (A1 ~^ A2)))
    );

    // When C1 is high, only the A1/A2/A3 term can drive Y.
    check_y_when_c1_high: assert property (
        @(posedge clk) disable iff (1'b0)
        C1 |-> (Y == (A1 & A2 & ~A3))
    );

    // When C1 is low, Y reduces to B1 OR equality of A1 and A2.
    check_y_when_c1_low: assert property (
        @(posedge clk) disable iff (1'b0)
        !C1 |-> (Y == (B1 | (A1 ~^ A2)))
    );

    // The explicit A1&A2&~A3 term always forces Y high.
    check_a_term_drives_y: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 & A2 & ~A3) |-> Y
    );

    // When C1 is low and A1 equals A2, the S5 path forces Y high.
    check_equal_a_inputs_drive_y_when_c1_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (!C1 && (A1 ~^ A2)) |-> Y
    );

    // When C1 is low, B1 is low, and A1 differs from A2, Y must be low.
    check_unequal_a_inputs_need_b1_when_c1_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (!C1 && !B1 && (A1 ^ A2)) |-> !Y
    );

    // With C1 high, A3 high blocks the A1&A2 term.
    check_a3_blocks_y_when_c1_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (C1 && A1 && A2 && A3) |-> !Y
    );

    // With C1 high, A3 low enables the A1&A2 term.
    check_a3_enables_y_when_c1_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (C1 && A1 && A2 && !A3) |-> Y
    );

endmodule