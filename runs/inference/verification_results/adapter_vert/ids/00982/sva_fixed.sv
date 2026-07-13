module components_dff_en_rst_sva (
    input logic clk,
    input logic contents,
    input logic d,
    input logic en,
    input logic q,
    input logic rst,
    input logic RESET_VAL,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> (contents) == (RESET_VAL); endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (rst) != 1'b1 && (en) |-> (contents) == (d); endproperty
assert property (EnableSynceotid);

property SyncLoadeotid; @(posedge clk) (rst) != 1'b1  |-> (q) == (contents); endproperty
assert property (SyncLoadeotid);

property ClockSynceotid; @(posedge clk) (en) |-> (contents) == (d) ; endproperty
assert property (ClockSynceotid);

property SyncLoadeotid_2; @(posedge clk)  |-> (q) == (contents); endproperty
assert property (SyncLoadeotid_2);

endmodule