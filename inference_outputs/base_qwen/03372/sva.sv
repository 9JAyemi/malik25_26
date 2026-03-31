```systemverilog
module mux4to1_sva(
    input logic [3:0] in,
    input logic [1:0] sel,
    output logic out
);
    // Mux output is one of the input signals based on the select signal
    mux_output: assert property (
        @(posedge clk) disable iff (!resetn) out == in[sel]
    );
    // Default case should not be reached
    default_case: assert property (
        @(posedge clk) disable iff (!resetn) $stable(out)
    );
endmodule
```