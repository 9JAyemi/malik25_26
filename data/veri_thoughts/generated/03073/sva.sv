module nor3_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);

    // Y must equal the 3-input NOR of A, B, and C.
    check_nor_equivalence: assert property (
        @(posedge clk) Y == ~(A | B | C)
    );

    // If all inputs are low, Y must be high.
    check_all_inputs_low_drives_y_high: assert property (
        @(posedge clk) (!A && !B && !C) |-> Y
    );

    // If any input is high, Y must be low.
    check_any_input_high_drives_y_low: assert property (
        @(posedge clk) (A || B || C) |-> !Y
    );

    // A high Y implies all three inputs are low.
    check_y_high_implies_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C)
    );

    // A low Y implies at least one input is high.
    check_y_low_implies_some_input_high: assert property (
        @(posedge clk) !Y |-> (A || B || C)
    );

endmodule