module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // EN low forces ENCLK high on rising-edge samples.
    check_en_low_rise_forces_high: assert property (
        @(posedge CLK) (EN == 1'b0) |-> (ENCLK == 1'b1)
    );

    // EN low forces ENCLK high on falling-edge samples.
    check_en_low_fall_forces_high: assert property (
        @(negedge CLK) (EN == 1'b0) |-> (ENCLK == 1'b1)
    );

    // EN high with TE low forces ENCLK low on rising-edge samples.
    check_te_low_rise_forces_low: assert property (
        @(posedge CLK) ((EN == 1'b1) && (TE == 1'b0)) |-> (ENCLK == 1'b0)
    );

    // EN high with TE low forces ENCLK low on falling-edge samples.
    check_te_low_fall_forces_low: assert property (
        @(negedge CLK) ((EN == 1'b1) && (TE == 1'b0)) |-> (ENCLK == 1'b0)
    );

    // EN and TE high make ENCLK follow CLK on rising-edge samples.
    check_clk_passthrough_rise: assert property (
        @(posedge CLK) ((EN == 1'b1) && (TE == 1'b1)) |-> (ENCLK == CLK)
    );

    // EN and TE high make ENCLK follow CLK on falling-edge samples.
    check_clk_passthrough_fall: assert property (
        @(negedge CLK) ((EN == 1'b1) && (TE == 1'b1)) |-> (ENCLK == CLK)
    );

endmodule

bind clock_gate_1 clock_gate_sva clock_gate_1_sva_bind (
    .CLK(CLK),
    .EN(EN),
    .TE(TE),
    .ENCLK(ENCLK)
);

bind clock_gate_2 clock_gate_sva clock_gate_2_sva_bind (
    .CLK(CLK),
    .EN(EN),
    .TE(TE),
    .ENCLK(ENCLK)
);