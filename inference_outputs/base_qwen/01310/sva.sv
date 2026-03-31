```systemverilog
module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    ///// Clock gating logic /////
    // ENCLK should be 1 when EN is 1 and TE is 1.
    clock_gating_1: assert property (
        @(posedge CLK) disable iff (!EN) ENCLK |-> (EN && TE)
    );
    // ENCLK should be 0 when EN is 0.
    clock_gating_2: assert property (
        @(posedge CLK) disable iff (!EN) !ENCLK |-> !EN
    );
    // ENCLK should be 0 when TE is 0 and EN is 1.
    clock_gating_3: assert property (
        @(posedge CLK) disable iff (!EN) !ENCLK |-> (!TE && EN)
    );
endmodule
```