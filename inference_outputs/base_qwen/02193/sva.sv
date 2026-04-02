module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    output logic [7:0] q
);
    // DFF should only update on the negative edge of the clock
    dff_update: assert property (
        @(negedge clk) disable iff (!clk) q == d
    );
endmodule