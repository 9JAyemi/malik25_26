```systemverilog
module xor_gate_sva (
    input logic A,
    input logic B,
    input logic X,
    input logic VPWR,
    input logic VGND
);
    // XOR gate behavior: X should be 1 if A and B are different, and 0 if they are the same.
    xor_behavior: assert property (
        @(posedge VPWR) disable iff (!VGND) (A != B) |-> X == 1'b1
    ) else $error("XOR gate output is incorrect when A and B are different.");

    xor_behavior_2: assert property (
        @(posedge VPWR) disable iff (!VGND) (A == B) |-> X == 1'b0
    ) else $error("XOR gate output is incorrect when A and B are the same.");
endmodule
```