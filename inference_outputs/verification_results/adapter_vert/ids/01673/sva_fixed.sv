module FSM_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic rst,
    input logic state,
    input logic I0,
    input logic I1,
    input logic O0,
    input logic O1,
    input logic S0,
    input logic S1,
    input logic S2,
    input logic S3
);

property ResetSynceotid; @(posedge clk) (rst) |-> (state == S0) && (out == O0) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) && (in == I0) |-> (state == S1) && (out == O0) ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (rst) && (in == I1) |-> (state == S2) && (out == O1) ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge clk) (rst) && (  (in != I0) &&  (in != I1)  ) |-> (state == S0) && (out == O0) ;endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(posedge clk) ! (rst) && (in == I0) |-> (state == S2) && (out == O0) ;endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(posedge clk) ! (rst) && (in == I1) |-> (state == S3) && (out == O1) ;endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(posedge clk) ! (rst) && (  (in != I0) &&  (in != I1)  ) |-> (state == S1) && (out == O0) ;endproperty
assert property (ResetSynceotid_7);

endmodule