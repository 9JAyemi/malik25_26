```systemverilog
module top_module_assertions (
    input logic clk,
    input logic [15:0] in,
    output logic [7:0] out_hi,
    output logic [7:0] out_lo
);

    // Sequential logic: out_hi and out_lo are updated on the rising edge of clk
    // out_hi should be the upper 8 bits of in
    property p_out_hi;
        @(posedge clk) disable iff (!clk) out_hi == in[15:8];
    endproperty
    assert property (p_out_hi) else $error("out_hi is not correctly set to the upper 8 bits of in");

    // Sequential logic: out_lo and out_lo are updated on the rising edge of clk
    // out_lo should be the lower 8 bits of in
    property p_out_lo;
        @(posedge clk) disable iff (!clk) out_lo == in[7:0];
    endproperty
    assert property (p_out_lo) else $error("out_lo is not correctly set to the lower 8 bits of in");

endmodule
```