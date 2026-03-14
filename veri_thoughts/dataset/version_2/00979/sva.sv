module pg_to_PG_sva (
    input logic clk,
    input logic [15:0] p,
    input logic [15:0] g,
    input logic [3:0] bp,
    input logic [3:0] bg
);

    ///// Block-generate definitions /////
    // bg[0] equals g[3] | p[3]&g[2] | p[3]&p[2]&g[1] | p[3]&p[2]&p[1]&g[0]
    check_bg0_definition: assert property (
        @(posedge clk) bg[0] == ( g[3]
                               | (p[3] & g[2])
                               | (p[3] & p[2] & g[1])
                               | (p[3] & p[2] & p[1] & g[0]) )
    );
    // bg[1] equals g[7] | p[7]&g[6] | p[7]&p[6]&g[5] | p[7]&p[6]&p[5]&g[4]
    check_bg1_definition: assert property (
        @(posedge clk) bg[1] == ( g[7]
                               | (p[7] & g[6])
                               | (p[7] & p[6] & g[5])
                               | (p[7] & p[6] & p[5] & g[4]) )
    );
    // bg[2] equals g[11] | p[11]&g[10] | p[11]&p[10]&g[9] | p[11]&p[10]&p[9]&g[8]
    check_bg2_definition: assert property (
        @(posedge clk) bg[2] == ( g[11]
                               | (p[11] & g[10])
                               | (p[11] & p[10] & g[9])
                               | (p[11] & p[10] & p[9] & g[8]) )
    );
    // bg[3] equals g[15] | p[15]&g[14] | p[15]&p[14]&g[13] | p[15]&p[14]&p[13]&g[12]
    check_bg3_definition: assert property (
        @(posedge clk) bg[3] == ( g[15]
                               | (p[15] & g[14])
                               | (p[15] & p[14] & g[13])
                               | (p[15] & p[14] & p[13] & g[12]) )
    );

    ///// Block-propagate definitions /////
    // bp[0] equals p[3]&p[2]&p[1]&p[0]
    check_bp0_definition: assert property (
        @(posedge clk) bp[0] == (p[3] & p[2] & p[1] & p[0])
    );
    // bp[1] equals p[7]&p[6]&p[5]&p[4]
    check_bp1_definition: assert property (
        @(posedge clk) bp[1] == (p[7] & p[6] & p[5] & p[4])
    );
    // bp[2] equals p[11]&p[10]&p[9]&p[8]
    check_bp2_definition: assert property (
        @(posedge clk) bp[2] == (p[11] & p[10] & p[9] & p[8])
    );
    // bp[3] equals p[15]&p[14]&p[13]&p[12]
    check_bp3_definition: assert property (
        @(posedge clk) bp[3] == (p[15] & p[14] & p[13] & p[12])
    );

    ///// Necessary conditions for block-generate /////
    // If bg[0] is 1, at least one g in [3:0] is 1.
    check_bg0_implies_some_g: assert property (
        @(posedge clk) bg[0] |-> (g[3] || g[2] || g[1] || g[0])
    );
    // If bg[1] is 1, at least one g in [7:4] is 1.
    check_bg1_implies_some_g: assert property (
        @(posedge clk) bg[1] |-> (g[7] || g[6] || g[5] || g[4])
    );
    // If bg[2] is 1, at least one g in [11:8] is 1.
    check_bg2_implies_some_g: assert property (
        @(posedge clk) bg[2] |-> (g[11] || g[10] || g[9] || g[8])
    );
    // If bg[3] is 1, at least one g in [15:12] is 1.
    check_bg3_implies_some_g: assert property (
        @(posedge clk) bg[3] |-> (g[15] || g[14] || g[13] || g[12])
    );

endmodule