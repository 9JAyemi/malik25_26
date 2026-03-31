```systemverilog
module and_or_module_sva (
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out
);
    // AND gate output should be the logical AND of a and b
    and_output: assert property (
        @(posedge clk) disable iff (!resetn) (g_out == (a & b))
    );

    // OR gate output should be the logical OR of a and b
    or_output: assert property (
        @(posedge clk) disable iff (!resetn) (p_out == (a | b))
    );
endmodule
```