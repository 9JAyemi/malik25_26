module arithmetic_module_sva (
    input logic Boo_ba1,
    input logic Boo_ba2,
    input logic Boo_ba3,
    input logic b,
    input logic c,
    input logic f1_dotnamed,
    input logic f2_dotnamed,
    input logic f3_dotnamed,
    input logic f4_dotnamed,
    input logic clk_in_13
);

property ClockSynceotid; @(posedge clk_in_13) (Boo_ba1) |-> (f1_dotnamed) == (Boo_ba1 << 1) ; endproperty
assert property (ClockSynceotid);

property AddSynceotid; @(posedge clk_in_13) (Boo_ba2) &&  (b) |-> (f2_dotnamed) == (Boo_ba2 + b) ; endproperty
assert property (AddSynceotid);

property SyncSubeotid; @(posedge clk_in_13) (Boo_ba3) &&  (c) |-> (f3_dotnamed) == (Boo_ba3 - c) ; endproperty
assert property (SyncSubeotid);

property SyncAdder; @(posedge clk_in_13) (Boo_ba1) |-> (f4_dotnamed) == (f1_dotnamed + f2_dotnamed + f3_dotnamed) ; endproperty
assert property (SyncAdder);

endmodule