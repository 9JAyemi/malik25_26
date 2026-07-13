module FP16RAddSubS2Of5_sva (
    input logic arg_2,
    input logic arg_3,
    input logic arg_5,
    input logic arg_6,
    input logic clk,
    input logic r_final,
    input logic rst,
    input logic rxy,
    input logic xn,
    input logic yn,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> xn == 0 && yn == 0 ;endproperty
assert property (ResetSynceotid);

property SyncCheckeotid; @(posedge clk) (rst) != 1'b1 |-> xn == arg_5 && yn == arg_6 ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (rst) != 1'b1  &&  (xn != yn) |-> rxy == arg_2 + arg_3 ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk) (rst) != 1'b1  &&  (xn != yn)  |->  r_final == (rxy + 1) ;endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk) (rst) != 1'b1  &&  (xn == yn)  |->  r_final == rxy ;endproperty
assert property (SyncCheckeotid_4);

endmodule