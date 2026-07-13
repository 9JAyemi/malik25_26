module nonblocking_gate_sva (
    input logic clk,
    input logic ctrl,
    input logic din,
    input logic dout,
    input logic sel,
    input logic b0000000
);

property ClockSynceotid; @(posedge clk) (dout) |-> (dout) == (din); endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk) (ctrl) && (sel) &&  (  (ctrl) && (sel)  != 7'b0000000 )  |->  (  (dout)  ==  (din)  ) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (ctrl) && (  !(sel)  )  &&  (  (ctrl)  != 7'b0000000 )  |->  (  (dout)  ==  (din)  ) ; endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk) (  !(ctrl)  )  &&  (  (sel)  != 0 )  |->  (  (dout)  ==  (din)  ) ; endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk) (  !(ctrl)  )  &&  (  !(sel)  )  |->  (  (dout)  ==  (din)  ) ; endproperty
assert property (SyncCheckeotid_4);

endmodule