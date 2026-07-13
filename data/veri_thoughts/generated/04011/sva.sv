module or4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // Y must equal the OR of all four inputs.
    check_y_matches_four_input_or: assert property (
        @(posedge clk) Y == (A | B | C | D)
    );

    // If all inputs are low, Y must be low.
    check_all_inputs_low_drive_y_low: assert property (
        @(posedge clk) !(A | B | C | D) |-> !Y
    );

    // A high must force Y high.
    check_a_high_drives_y_high: assert property (
        @(posedge clk) A |-> Y
    );

    // B high must force Y high.
    check_b_high_drives_y_high: assert property (
        @(posedge clk) B |-> Y
    );

    // C high must force Y high.
    check_c_high_drives_y_high: assert property (
        @(posedge clk) C |-> Y
    );

    // D high must force Y high.
    check_d_high_drives_y_high: assert property (
        @(posedge clk) D |-> Y
    );

    // Y low implies all inputs are low.
    check_y_low_implies_all_inputs_low: assert property (
        @(posedge clk) !Y |-> !(A | B | C | D)
    );

    // Y high implies at least one input is high.
    check_y_high_implies_any_input_high: assert property (
        @(posedge clk) Y |-> (A | B | C | D)
    );

endmodule