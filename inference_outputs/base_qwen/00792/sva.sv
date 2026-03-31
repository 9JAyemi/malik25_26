```systemverilog
module xor_module_sva(
    input logic a,
    input logic b,
    input logic out_comb_logic
);
    // Combinational logic: out_comb_logic should always be the XOR of a and b
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (out_comb_logic == (a ^ b))
    );
endmodule
```