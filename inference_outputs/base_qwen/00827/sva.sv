```systemverilog
module Test_assertions (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] out
);
    // The logic is purely combinational as there is no clock signal.

    // out should be equal to a when a is greater than or equal to b.
    max_check: assert property (
        @(posedge clk) disable iff (!RESETn) (a >= b) |-> (out == a)
    );

    // out should be equal to b when b is greater than a.
    min_check: assert property (
        @(posedge clk) disable iff (!RESETn) (b > a) |-> (out == b)
    );

    // out should be 0 when a is equal to b.
    zero_check: assert property (
        @(posedge clk) disable iff (!RESETn) (a == b) |-> (out == 0)
    );
endmodule
```