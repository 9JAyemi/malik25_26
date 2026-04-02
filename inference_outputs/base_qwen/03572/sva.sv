module ClockGating_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic RESET,
    output logic ENCLK
);
    ///// Clock gating logic /////
    // ENCLK is LOW when RESET is asserted.
    reset: assert property (
        @(posedge CLK) disable iff (!RESET) RESET |-> (ENCLK == 1'b0)
    );
    // ENCLK is LOW when EN is LOW.
    enable_low: assert property (
        @(posedge CLK) disable iff (!RESET) !EN |-> (ENCLK == 1'b0)
    );
    // ENCLK is the inverse of CLK when EN is HIGH and TE is LOW.
    enable_high_te_low: assert property (
        @(posedge CLK) disable iff (!RESET) EN && !TE |-> (ENCLK == ~CLK)
    );
    // ENCLK is LOW when EN is HIGH and TE is HIGH.
    enable_high_te_high: assert property (
        @(posedge CLK) disable iff (!RESET) EN && TE |-> (ENCLK == 1'b0)
    );
endmodule