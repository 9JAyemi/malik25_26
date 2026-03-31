```systemverilog
module comparator_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic gt,
    input logic lt,
    input logic eq
);
    // gt should be set to 1 when a > b
    gt_check: assert property (
        @(posedge clk) disable iff (!reset_n) (a > b) |-> gt
    );
    // lt should be set to 1 when a < b
    lt_check: assert property (
        @(posedge clk) disable iff (!reset_n) (a < b) |-> lt
    );
    // eq should be set to 1 when a == b
    eq_check: assert property (
        @(posedge clk) disable iff (!reset_n) (a == b) |-> eq
    );
    // gt, lt, and eq should not be set to 1 at the same time
    exclusive_check: assert property (
        @(posedge clk) disable iff (!reset_n) !(gt && lt) && !(gt && eq) && !(lt && eq)
    );
endmodule
```