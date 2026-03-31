```systemverilog
module addition_module_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum,
    input logic carry
);
    // Combinational logic: sum and carry are determined by A and B
    // sum is the result of adding A and B
    // carry is 1 if the sum exceeds 255, otherwise 0
    comb_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (sum == A + B) && (carry == (A + B > 255 ? 1 : 0))
    );
endmodule
```