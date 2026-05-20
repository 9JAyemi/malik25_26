module counter_sva (
    input logic clk,
    input logic count,
    input logic en,
    input logic rst,
    input logic b00,
    input logic b11
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 2'b00 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) &&  (en) &&  (count != 2'b11)  |-> count == count + 1 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (rst) &&  (en) &&  (count == 2'b11)  |-> count == 2'b00 ;endproperty
assert property (ResetSynceotid_3);

endmodule