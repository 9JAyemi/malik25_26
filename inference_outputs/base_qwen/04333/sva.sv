```systemverilog
module bw_clk_gclk_inv_r90_192x_sva (
    input logic clk,
    input logic clkin,
    output logic clkout
);
    // Combinational logic: clkout is the inverse of clkin
    comb_logic: assert property (
        @(posedge clk) disable iff (!clk) clkout == ~clkin
    );
endmodule
```