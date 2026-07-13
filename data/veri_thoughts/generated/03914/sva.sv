module my_logic_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X must equal C1 OR B1 OR (A1 AND A2).
    check_output_equation: assert property (
        @(posedge clk) X == (C1 | B1 | (A1 & A2))
    );

    // C1 high must drive X high through the OR gate.
    check_c1_drives_x_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // B1 high must drive X high through the OR gate.
    check_b1_drives_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // A1 and A2 high together must drive X high through the AND term.
    check_a1_a2_drive_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // If all OR inputs are low, X must be low.
    check_all_terms_low_drive_x_low: assert property (
        @(posedge clk) (!C1 && !B1 && !(A1 & A2)) |-> !X
    );

endmodule