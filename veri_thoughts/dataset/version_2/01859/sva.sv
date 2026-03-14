module top_module_sva (
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo,
    input logic        clk
);
    // DUT: top_module | Clock: clk (posedge) | Reset: none | Logic: mixed (comb split + seq regs)

    // Outputs are the 1-cycle delayed split of input (full 16-bit check).
    check_pipeline_concat: assert property (
        @(posedge clk) 1'b1 |=> {out_hi, out_lo} == $past(in)
    );

    // High byte output equals previous cycle's in[15:8].
    check_pipeline_hi: assert property (
        @(posedge clk) 1'b1 |=> out_hi == $past(in[15:8])
    );

    // Low byte output equals previous cycle's in[7:0].
    check_pipeline_lo: assert property (
        @(posedge clk) 1'b1 |=> out_lo == $past(in[7:0])
    );

endmodule