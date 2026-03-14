module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // Analysis: No reset in RTL; sample assertions on CLK. Combinational logic: ENCLK updates on EN/TE changes.
    // Behavior: if EN==1 then ENCLK=CLK (sampled when EN/TE change); else if TE==1 then ENCLK=0; else ENCLK=X.

    ///// Functional checks /////
    // When EN=0 and TE=1, ENCLK is forced LOW.
    check_force_low_when_te_and_not_en: assert property (
        @(posedge CLK) (!EN && TE) |-> (ENCLK == 1'b0)
    );

    // If EN=0 and TE=1 hold across two sampled cycles, ENCLK is LOW on the later cycle.
    check_hold_low_across_two_cycles: assert property (
        @(posedge CLK) ((!EN && TE) ##1 (!EN && TE)) |-> (ENCLK == 1'b0)
    );
endmodule