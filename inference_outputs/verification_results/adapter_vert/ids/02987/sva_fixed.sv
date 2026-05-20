module calculator_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic op,
    input logic overflow,
    input logic result
);

property AddSynceotid; @(posedge clk) (op) |-> result == a - b ; endproperty
assert property (AddSynceotid);

property AddSynceotid_2; @(posedge clk) (op) != 1 |-> result == a + b ; endproperty
assert property (AddSynceotid_2);

property SafeSynceotid; @(posedge clk) (result[7] == 1 && op == 0 && a[7] == 1 && b[7] == 1) || (result[7] == 1 && op == 1 && a[7] == 0 && b[7] == 1) || (result[7] == 0 && op == 1 && a[7] == 1 && b[7] == 0) |-> overflow == 1 ; endproperty
assert property (SafeSynceotid);

endmodule