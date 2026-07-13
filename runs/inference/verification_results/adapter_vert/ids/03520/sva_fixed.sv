module counter_sva (
    input logic clk,
    input logic count,
    input logic rst,
    input logic b0,
    input logic h10,
    input logic reg_1
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 8'b0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) |->  (  count  != 8'h10  ) ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (rst) |->  (  reg_1  != 8'h10  ) ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge clk) (rst) |->  (  reg_1  != 8'h10  ) ;endproperty
assert property (ResetSynceotid_4);

endmodule