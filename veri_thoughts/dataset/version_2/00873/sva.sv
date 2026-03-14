module sky130_fd_sc_hd__a211oi_sva (
    input logic clk,   // Sampling clock for SVA (DUT is purely combinational)
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    ///// Functional equivalence /////
    // Y must equal ~((A1 & A2) | B1 | C1) with 4-state accuracy.
    check_function_equivalence: assert property (
        @(posedge clk) (Y === ~((A1 & A2) | B1 | C1))
    );

    ///// Dominating inputs drive Y LOW /////
    // If B1 is HIGH, Y must be LOW.
    check_y_low_when_B1_high: assert property (
        @(posedge clk) (B1 == 1'b1) |-> (Y == 1'b0)
    );
    // If C1 is HIGH, Y must be LOW.
    check_y_low_when_C1_high: assert property (
        @(posedge clk) (C1 == 1'b1) |-> (Y == 1'b0)
    );
    // If A1 and A2 are both HIGH, Y must be LOW.
    check_y_low_when_A1A2_both_high: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    ///// Conditions that force Y HIGH /////
    // If B1=0, C1=0, and A1=0, Y must be HIGH.
    check_y_high_when_B1C1_low_A1_low: assert property (
        @(posedge clk) ((B1 == 1'b0) && (C1 == 1'b0) && (A1 == 1'b0)) |-> (Y == 1'b1)
    );
    // If B1=0, C1=0, and A2=0, Y must be HIGH.
    check_y_high_when_B1C1_low_A2_low: assert property (
        @(posedge clk) ((B1 == 1'b0) && (C1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    ///// Necessary conditions derived from Y /////
    // If Y is HIGH, then B1=0, C1=0, and (A1 & A2)=0.
    check_y_high_implies_terms_low: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((B1 == 1'b0) && (C1 == 1'b0) && ((A1 & A2) == 1'b0))
    );
    // If Y is LOW, then (A1 & A2)=1 or B1=1 or C1=1.
    check_y_low_implies_some_term_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (((A1 & A2) == 1'b1) || (B1 == 1'b1) || (C1 == 1'b1))
    );

    ///// Specific minterms /////
    // When A1=A2=B1=C1=0, Y must be 1.
    check_minterm_all_zero: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b0) && (C1 == 1'b0)) |-> (Y == 1'b1)
    );
    // When A1=A2=B1=C1=1, Y must be 0.
    check_minterm_all_one: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );
endmodule