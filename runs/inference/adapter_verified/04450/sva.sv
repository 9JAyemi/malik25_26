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

// DE high loads D on the next clock.
    check_de_loads_d: assert property (
        @(posedge CLK) DE |=> (Q == $past(D))
    );

// DE high has priority over SCE when both are high.
    check_de_priority_over_sce: assert property (
        @(posedge CLK) (DE && SCE) |=> (Q == $past(D))
    );

// SCE high loads SCD when DE is low.
    check_sce_loads_scd: assert property (
        @(posedge CLK) (!DE && SCE) |=> (Q == $past(SCD))
    );

// With both controls low, Q holds its previous value.
    check_hold_when_idle: assert property (
        @(posedge CLK) (!DE && !SCE) |=> (Q == $past(Q))
    );

// A high DE followed by a high SCE loads D on the next clock.
    check_de_then_sce_loads_d: assert property (
        @(posedge CLK) (DE ##1 SCE) |=> (Q == $past(D))
    );

// A high SCE followed by a high DE loads SCD on the next clock.
    check_sce_then_de_loads_scd: assert property (
        @(posedge CLK) (SCE ##1 DE) |=> (Q == $past(SCD))
    );

endmodule
