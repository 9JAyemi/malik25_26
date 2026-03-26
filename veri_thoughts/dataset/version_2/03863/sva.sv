module SNPS_CLOCK_GATE_HIGH_FSM_Mult_Function_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic CLK2,
    input logic SEL,
    input logic ENCLK
);

    // When SEL chooses CLK2, ENCLK must equal CLK2 gated by EN.
    check_enclk_matches_clk2_path: assert property (
        @(posedge CLK) SEL |-> (ENCLK == (CLK2 & EN))
    );

    // When SEL chooses CLK, ENCLK must equal CLK gated by EN.
    check_enclk_matches_clk_path: assert property (
        @(posedge CLK2) !SEL |-> (ENCLK == (CLK & EN))
    );

    // CLK edges must not disturb ENCLK when the CLK2 path inputs stay unchanged.
    check_clk_edge_ignored_when_clk2_selected: assert property (
        @(posedge CLK) !$initstate && SEL && $stable(SEL) && $stable(CLK2) && $stable(EN) |-> $stable(ENCLK)
    );

    // CLK2 edges must not disturb ENCLK when the CLK path inputs stay unchanged.
    check_clk2_edge_ignored_when_clk_selected: assert property (
        @(posedge CLK2) !$initstate && !SEL && $stable(SEL) && $stable(CLK) && $stable(EN) |-> $stable(ENCLK)
    );

endmodule