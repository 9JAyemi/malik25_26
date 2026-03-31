```systemverilog
module mag_comparator_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic EQ,
    input logic GT,
    input logic LT
);
    // EQ should be HIGH when A is equal to B
    eq_check: assert property (
        @(posedge CLK) disable iff (!RESETn) EQ |-> (A == B)
    );

    // GT should be HIGH when A is greater than B
    gt_check: assert property (
        @(posedge CLK) disable iff (!RESETn) GT |-> (A > B)
    );

    // LT should be HIGH when A is less than B
    lt_check: assert property (
        @(posedge CLK) disable iff (!RESETn) LT |-> (A < B)
    );

    // Only one of EQ, GT, or LT should be HIGH at any time
    one_hot_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (EQ + GT + LT) == 1'b1
    );

    // EQ, GT, and LT should be mutually exclusive
    mutual_exclusion_check: assert property (
        @(posedge CLK) disable iff (!RESETn) !(EQ && GT) && !(EQ && LT) && !(GT && LT)
    );

    // EQ should be LOW when A is not equal to B
    eq_neg_check: assert property (
        @(posedge CLK) disable iff (!RESETn) !EQ |-> (A != B)
    );

    // GT should be LOW when A is not greater than B
    gt_neg_check: assert property (
        @(posedge CLK) disable iff (!RESETn) !GT |-> (A <= B)
    );

    // LT should be LOW when A is not less than B
    lt_neg_check: assert property (
        @(posedge CLK) disable iff (!RESETn) !LT |-> (A >= B)
    );

    // EQ, GT, and LT should be LOW when A and B are equal
    eq_gt_lt_neg_check: assert property (
        @(posedge CLK) disable iff (!RESETn) !(EQ && GT && LT) |-> (A == B)
    );

    // EQ, GT, and LT should be LOW when A and B are not equal
    eq_gt_lt_neg_check_2: assert property (
        @(posedge CLK) disable iff (!RESETn) !(EQ && GT && LT) |-> (A != B)
    );
endmodule
```