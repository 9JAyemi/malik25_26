module sky130_fd_sc_ms__a2111oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y matches the RTL sum-of-products expression.
    check_y_matches_rtl_function: assert property (
        @($global_clock)
        Y == ((A1 & A2 & B1 & C1 & D1) |
              (A1 & A2 & ~B1 & C1 & D1) |
              (A1 & A2 & B1 & ~C1 & D1) |
              (A1 & A2 & B1 & C1 & ~D1) |
              (~A1 & ~A2 & B1 & C1 & D1) |
              (~A1 & ~A2 & ~B1 & C1 & D1) |
              (~A1 & ~A2 & B1 & ~C1 & D1) |
              (~A1 & ~A2 & B1 & C1 & ~D1) |
              (~A1 & A2 & B1 & C1 & D1) |
              (~A1 & A2 & ~B1 & C1 & D1) |
              (~A1 & A2 & B1 & ~C1 & D1) |
              (~A1 & A2 & B1 & C1 & ~D1) |
              (A1 & ~A2 & B1 & C1 & D1) |
              (A1 & ~A2 & ~B1 & C1 & D1) |
              (A1 & ~A2 & B1 & ~C1 & D1) |
              (A1 & ~A2 & B1 & C1 & ~D1))
    );

    // All high inputs force Y high.
    check_all_high_forces_y_high: assert property (
        @($global_clock)
        (A1 & A2 & B1 & C1 & D1) |-> Y
    );

    // All low inputs force Y high.
    check_all_low_forces_y_high: assert property (
        @($global_clock)
        (~A1 & ~A2 & ~B1 & ~C1 & ~D1) |-> Y
    );

    // Any mixed A1/A2 pair with B1/C1/D1 high forces Y high.
    check_mixed_a1a2_with_bcd_high_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & B1 & C1 & D1) |
         (~A1 & A2 & B1 & C1 & D1)) |-> Y
    );

    // Any mixed A1/A2 pair with B1/C1/D1 low forces Y high.
    check_mixed_a1a2_with_bcd_low_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & ~B1 & ~C1 & ~D1) |
         (~A1 & A2 & ~B1 & ~C1 & ~D1)) |-> Y
    );

    // Any mixed A1/A2 pair with B1/C1 high and D1 low forces Y high.
    check_mixed_a1a2_with_bcd_mixed_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & B1 & C1 & ~D1) |
         (~A1 & A2 & B1 & C1 & ~D1)) |-> Y
    );

    // Any mixed A1/A2 pair with B1/C1 low and D1 high forces Y high.
    check_mixed_a1a2_with_bcd_mixed_reverse_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & ~B1 & ~C1 & D1) |
         (~A1 & A2 & ~B1 & ~C1 & D1)) |-> Y
    );

    // Any mixed A1/A2 pair with B1 high and C1/D1 low forces Y high.
    check_mixed_a1a2_with_bd_mixed_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & B1 & ~C1 & ~D1) |
         (~A1 & A2 & B1 & ~C1 & ~D1)) |-> Y
    );

    // Any mixed A1/A2 pair with B1 low and C1/D1 high forces Y high.
    check_mixed_a1a2_with_bd_mixed_reverse_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & ~B1 & C1 & D1) |
         (~A1 & A2 & ~B1 & C1 & D1)) |-> Y
    );

    // Any mixed A1/A2 pair with C1 high and D1 low forces Y high.
    check_mixed_a1a2_with_cd_mixed_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & ~B1 & C1 & ~D1) |
         (~A1 & A2 & ~B1 & C1 & ~D1)) |-> Y
    );

    // Any mixed A1/A2 pair with C1 low and D1 high forces Y high.
    check_mixed_a1a2_with_cd_mixed_reverse_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & ~B1 & ~C1 & D1) |
         (~A1 & A2 & ~B1 & ~C1 & D1)) |-> Y
    );

    // Any mixed A1/A2 pair with B1 high and C1/D1 mixed forces Y high.
    check_mixed_a1a2_with_bcd_mixed_with_bd_mixed_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & B1 & ~C1 & D1) |
         (~A1 & A2 & B1 & ~C1 & D1)) |-> Y
    );

    // Any mixed A1/A2 pair with B1 low and C1/D1 mixed forces Y high.
    check_mixed_a1a2_with_bcd_mixed_with_bd_mixed_reverse_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & ~B1 & C1 & D1) |
         (~A1 & A2 & ~B1 & C1 & D1)) |-> Y
    );

    // Any mixed A1/A2 pair with C1 high and D1 mixed forces Y high.
    check_mixed_a1a2_with_cd_mixed_with_bd_mixed_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & ~B1 & C1 & ~D1) |
         (~A1 & A2 & ~B1 & C1 & ~D1)) |-> Y
    );

    // Any mixed A1/A2 pair with C1 low and D1 mixed forces Y high.
    check_mixed_a1a2_with_cd_mixed_with_bd_mixed_reverse_forces_y_high: assert property (
        @($global_clock)
        ((A1 & ~A2 & ~B1 & ~C1 & D1) |
         (~A1 & A2 & ~B1 & ~C1 & D1)) |-> Y
    );

endmodule