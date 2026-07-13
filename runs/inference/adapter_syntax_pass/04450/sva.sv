module flip_flop_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic DE,
    input logic SCD,
    input logic SCE,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Q follows D when DE is high.
    check_load_d_when_enabled: assert property (
        @(posedge CLK) DE |=> (Q == $past(D))
    );

    // Q follows SCD when DE is low and SCE is high.
    check_load_scd_when_enabled: assert property (
        @(posedge CLK) (!DE && SCE) |=> (Q == $past(SCD))
    );

    // Q holds its value when both enables are low.
    check_hold_when_disabled: assert property (
        @(posedge CLK) (!DE && !SCE) |=> (Q == $past(Q))
    );

endmodule