module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic RST,
    input logic ENCLK
);

// Reset forces ENCLK low on the next clock.
    check_reset_clears_enclk: assert property (
        @(posedge CLK) RST |=> (ENCLK == 1'b0)
    );

// TE high with EN high loads ENCLK high on the next clock.
    check_enable_loads_high: assert property (
        @(posedge CLK) disable iff (RST) TE && EN |=> (ENCLK == 1'b1)
    );

// TE high with EN low loads ENCLK low on the next clock.
    check_enable_loads_low: assert property (
        @(posedge CLK) disable iff (RST) TE && !EN |=> (ENCLK == 1'b0)
    );

// TE low holds ENCLK high when it was high.
    check_hold_high_when_te_low: assert property (
        @(posedge CLK) disable iff (RST) !TE && ENCLK |=> (ENCLK == 1'b1)
    );

// TE low holds ENCLK low when it was low.
    check_hold_low_when_te_low: assert property (
        @(posedge CLK) disable iff (RST) !TE && !ENCLK |=> (ENCLK == 1'b0)
    );

endmodule
