module clock_generator_sva (
    input logic CLK_24M,
    input logic RESETP,
    input logic CLK_24MB,
    input logic LSPC_12M,
    input logic LSPC_8M,
    input logic LSPC_6M,
    input logic LSPC_4M,
    input logic LSPC_3M,
    input logic LSPC_1_5M,
    input logic Q53_CO
);

    // The inverted clock must be high when CLK_24M rises.
    check_clk_24mb_inverts_clk_24m_rise: assert property (
        @(posedge CLK_24M) disable iff (!RESETP)
        (CLK_24MB == 1'b1)
    );

    // The source clock must be high when CLK_24MB rises.
    check_clk_24m_inverts_clk_24mb_rise: assert property (
        @(posedge CLK_24MB) disable iff (!RESETP)
        (CLK_24M == 1'b1)
    );

    // Reset forces the externally visible outputs to their reset values.
    check_reset_drives_defined_outputs: assert property (
        @(posedge CLK_24M)
        !RESETP |-> (
            (Q53_CO    == 1'b1) &&
            (LSPC_1_5M == 1'b1) &&
            (LSPC_8M   == 1'b1) &&
            (LSPC_6M   == 1'b1) &&
            (LSPC_4M   == 1'b0) &&
            (LSPC_12M  == 1'b0) &&
            (LSPC_3M   == 1'b0)
        )
    );

    // LSPC_6M being selected excludes the other decoded outputs.
    check_lspc_6m_decode_exclusive: assert property (
        @(posedge CLK_24M) disable iff (!RESETP)
        LSPC_6M |-> (!LSPC_4M && !LSPC_12M && !LSPC_3M)
    );

    // LSPC_4M being selected excludes the other decoded outputs.
    check_lspc_4m_decode_exclusive: assert property (
        @(posedge CLK_24M) disable iff (!RESETP)
        LSPC_4M |-> (!LSPC_6M && !LSPC_12M && !LSPC_3M)
    );

    // LSPC_12M being selected excludes the other decoded outputs.
    check_lspc_12m_decode_exclusive: assert property (
        @(posedge CLK_24M) disable iff (!RESETP)
        LSPC_12M |-> (!LSPC_6M && !LSPC_4M && !LSPC_3M)
    );

    // LSPC_3M being selected excludes the other decoded outputs.
    check_lspc_3m_decode_exclusive: assert property (
        @(posedge CLK_24M) disable iff (!RESETP)
        LSPC_3M |-> (!LSPC_6M && !LSPC_4M && !LSPC_12M)
    );

    // The decoded counter outputs must always have an active selection.
    check_decode_has_active_output: assert property (
        @(posedge CLK_24M) disable iff (!RESETP)
        (LSPC_6M || LSPC_4M || LSPC_12M || LSPC_3M)
    );

    // Q53_CO becomes high after a CLK_24M edge.
    check_q53_co_converges_high: assert property (
        @(posedge CLK_24M) disable iff (!RESETP)
        1'b1 |=> (Q53_CO == 1'b1)
    );

    // LSPC_8M becomes high after a CLK_24M edge.
    check_lspc_8m_converges_high: assert property (
        @(posedge CLK_24M) disable iff (!RESETP)
        1'b1 |=> (LSPC_8M == 1'b1)
    );

endmodule