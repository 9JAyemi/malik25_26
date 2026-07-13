module top_module_sva (
    input logic a,
    input logic ab_min,
    input logic abcd_min,
    input logic b,
    input logic c,
    input logic d,
    input logic min,
    input logic cd_min,
    input logic clk_in_1
);

property MinAeotid; @(posedge clk_in_1) (a) < (b) |-> (ab_min) == (a) ; endproperty
assert property (MinAeotid);

property MinCdeotid; @(posedge clk_in_1) (c) < (d) |-> (cd_min) == (c) ; endproperty
assert property (MinCdeotid);

property MinValideotid; @(posedge clk_in_1) (ab_min) < (cd_min) |-> (abcd_min) == (ab_min) ; endproperty
assert property (MinValideotid);

property MinValideotid_2; @(posedge clk_in_1) (a) < (b) && (c) < (d)  |-> (min) == (ab_min) ; endproperty
assert property (MinValideotid_2);

endmodule