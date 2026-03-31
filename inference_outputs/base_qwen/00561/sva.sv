```systemverilog
module SimpleCalculator_assertions (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic op,
    input logic [3:0] result
);
    // Addition operation should produce correct result
    add_check: assert property (
        @(posedge clk) disable iff (!resetn) (op == 0) |-> (result == a + b)
    );
    // Subtraction operation should produce correct result
    sub_check: assert property (
        @(posedge clk) disable iff (!resetn) (op == 1) |-> (result == a - b)
    );
endmodule
```