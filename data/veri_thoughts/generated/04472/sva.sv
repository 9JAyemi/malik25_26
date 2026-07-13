module sky130_fd_sc_ms__o2111ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Y must match the O2111AI Boolean function.
    check_y_matches_o2111ai_function: assert property (
        @(posedge clk) Y == ~(((A1 | A2) & B1 & C1 & D1))
    );

    // If every NAND input is high, Y must be low.
    check_y_low_when_all_terms_high: assert property (
        @(posedge clk) ((A1 | A2) & B1 & C1 & D1) |-> !Y
    );

    // A low Y means the OR term and all other NAND inputs are high.
    check_y_low_implies_all_terms_high: assert property (
        @(posedge clk) !Y |-> ((A1 | A2) & B1 & C1 & D1)
    );

    // If both A inputs are low, Y must be high.
    check_y_high_when_a_inputs_low: assert property (
        @(posedge clk) !(A1 | A2) |-> Y
    );

    // A low B1 forces Y high.
    check_y_high_when_b1_low: assert property (
        @(posedge clk) !B1 |-> Y
    );

    // A low C1 forces Y high.
    check_y_high_when_c1_low: assert property (
        @(posedge clk) !C1 |-> Y
    );

    // A low D1 forces Y high.
    check_y_high_when_d1_low: assert property (
        @(posedge clk) !D1 |-> Y
    );

endmodule