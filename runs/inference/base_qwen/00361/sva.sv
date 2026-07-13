module d_ff_en_gate_sva (
    input logic CLK,
    input logic D,
    input logic EN,
    input logic TE,
    input logic Q,
    input logic ENCLK
);
    // Sequential logic driven by gated clock
    // ENCLK should be the same as gated_clk
    gated_clk_check: assert property (
        @(posedge CLK) disable iff (!CLK) ENCLK == ENCLK
    );

    // Q should only change on the rising edge of gated_clk when EN is high
    q_change_check: assert property (
        @(posedge CLK) disable iff (!CLK) (EN == 1'b1) |-> $rose(Q)
    );

    // Q should be equal to D when EN is high and TE is high
    q_equal_d_check: assert property (
        @(posedge CLK) disable iff (!CLK) (EN == 1'b1) && (TE == 1'b1) |-> Q == D
    );

    // Q should be 0 when EN is low
    q_zero_when_en_low_check: assert property (
        @(posedge CLK) disable iff (!CLK) (EN == 1'b0) |-> Q == 1'b0
    );

    // ENCLK should be 0 when TE is low
    enclk_zero_when_te_low_check: assert property (
        @(posedge CLK) disable iff (!CLK) (TE == 1'b0) |-> ENCLK == 1'b0
    );

    // ENCLK should be 0 when CLK is low
    enclk_zero_when_clk_low_check: assert property (
        @(posedge CLK) disable iff (!CLK) !CLK |-> ENCLK == 1'b0
    );

    // Q should be 0 when CLK is low
    q_zero_when_clk_low_check: assert property (
        @(posedge CLK) disable iff (!CLK) !CLK |-> Q == 1'b0
    );

    // ENCLK should be 0 when EN is low
    enclk_zero_when_en_low_check: assert property (
        @(posedge CLK) disable iff (!CLK) (EN == 1'b0) |-> ENCLK == 1'b0
    );

    // Q should be 0 when CLK is low
    q_zero_when_clk_low_check: assert property (
        @(posedge CLK) disable iff (!CLK) !CLK |-> Q == 1'b0
    );

    // ENCLK should be 0 when CLK is low
    enclk_zero_when_clk_low_check: assert property (
        @(posedge CLK) disable iff (!CLK) !CLK |-> ENCLK == 1'b0
    );

endmodule