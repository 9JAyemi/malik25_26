module pg_to_PG_assert (
    input logic clk,
    input logic [15:0] p,
    input logic [15:0] g,
    input logic [3:0] bp,
    input logic [3:0] bg
);
    // No clock/reset in RTL; purely combinational; assertions are clocked on clk.

    ///// Functional equivalence to RTL equations /////
    // bg[0] equals block-generate for bits [3:0].
    check_bg0_definition: assert property (
        @(posedge clk) bg[0] == ( g[3] | (p[3] & g[2]) | (p[3] & p[2] & g[1]) | (p[3] & p[2] & p[1] & g[0]) )
    );
    // bg[1] equals block-generate for bits [7:4].
    check_bg1_definition: assert property (
        @(posedge clk) bg[1] == ( g[7] | (p[7] & g[6]) | (p[7] & p[6] & g[5]) | (p[7] & p[6] & p[5] & g[4]) )
    );
    // bg[2] equals block-generate for bits [11:8].
    check_bg2_definition: assert property (
        @(posedge clk) bg[2] == ( g[11] | (p[11] & g[10]) | (p[11] & p[10] & g[9]) | (p[11] & p[10] & p[9] & g[8]) )
    );
    // bg[3] equals block-generate for bits [15:12].
    check_bg3_definition: assert property (
        @(posedge clk) bg[3] == ( g[15] | (p[15] & g[14]) | (p[15] & p[14] & g[13]) | (p[15] & p[14] & p[13] & g[12]) )
    );

    // bp[0] equals AND of p[3:0].
    check_bp0_definition: assert property (
        @(posedge clk) bp[0] == (p[3] & p[2] & p[1] & p[0])
    );
    // bp[1] equals AND of p[7:4].
    check_bp1_definition: assert property (
        @(posedge clk) bp[1] == (p[7] & p[6] & p[5] & p[4])
    );
    // bp[2] equals AND of p[11:8].
    check_bp2_definition: assert property (
        @(posedge clk) bp[2] == (p[11] & p[10] & p[9] & p[8])
    );
    // bp[3] equals AND of p[15:12].
    check_bp3_definition: assert property (
        @(posedge clk) bp[3] == (p[15] & p[14] & p[13] & p[12])
    );

    ///// Stability with respect to relevant inputs /////
    // bg[0] stable when p[3],p[2],p[1] and g[3:0] are stable.
    stable_bg0_on_group_inputs: assert property (
        @(posedge clk) $stable({p[3],p[2],p[1],g[3:0]}) |-> $stable(bg[0])
    );
    // bg[1] stable when p[7],p[6],p[5] and g[7:4] are stable.
    stable_bg1_on_group_inputs: assert property (
        @(posedge clk) $stable({p[7],p[6],p[5],g[7:4]}) |-> $stable(bg[1])
    );
    // bg[2] stable when p[11],p[10],p[9] and g[11:8] are stable.
    stable_bg2_on_group_inputs: assert property (
        @(posedge clk) $stable({p[11],p[10],p[9],g[11:8]}) |-> $stable(bg[2])
    );
    // bg[3] stable when p[15],p[14],p[13] and g[15:12] are stable.
    stable_bg3_on_group_inputs: assert property (
        @(posedge clk) $stable({p[15],p[14],p[13],g[15:12]}) |-> $stable(bg[3])
    );

    // bp[0] stable when p[3:0] are stable.
    stable_bp0_on_group_inputs: assert property (
        @(posedge clk) $stable(p[3:0]) |-> $stable(bp[0])
    );
    // bp[1] stable when p[7:4] are stable.
    stable_bp1_on_group_inputs: assert property (
        @(posedge clk) $stable(p[7:4]) |-> $stable(bp[1])
    );
    // bp[2] stable when p[11:8] are stable.
    stable_bp2_on_group_inputs: assert property (
        @(posedge clk) $stable(p[11:8]) |-> $stable(bp[2])
    );
    // bp[3] stable when p[15:12] are stable.
    stable_bp3_on_group_inputs: assert property (
        @(posedge clk) $stable(p[15:12]) |-> $stable(bp[3])
    );
endmodule