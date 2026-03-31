```systemverilog
module xor_gate_assertions (
    input logic a,
    input logic b,
    input logic y
);
    // XOR gate behavior: y should be 1 if a and b are different, and 0 if they are the same.
    xor_behavior: assert property (
        @(posedge clk) disable iff (!reset_n) (a != b) |-> (y == 1'b1) else (y == 1'b0)
    );
endmodule
```