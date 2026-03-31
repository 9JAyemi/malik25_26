```systemverilog
module xor_gate_sva (
    input logic a,
    input logic b,
    input logic out_comb
);
    // Combinational logic: out_comb should be (a & ~b) | (~a & b)
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (out_comb == ((a & ~b) | (~a & b)))
    );
endmodule
```