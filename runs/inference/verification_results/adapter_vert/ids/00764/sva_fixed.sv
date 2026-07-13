module xor_inv_multiplexer_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic out_always,
    input logic out_logical_inv,
    input logic out_xor,
    input logic out_xor_inv,
    input logic sel_b1,
    input logic sel_b2,
    input logic sel_out,
    input logic selected_input_b1,
    input logic selected_input_b2
);

property ClockSynceotid; @(posedge clk) (sel_b1) |-> selected_input_b1 == b ;endproperty
assert property (ClockSynceotid);

property SyncEqeotid; @(posedge clk) (sel_b1) &&  (  !(sel_b2)  &&  (sel_out) ) |-> selected_input_b2 == b ;endproperty
assert property (SyncEqeotid);

property XorSynceotid; @(posedge clk) (sel_b1) &&  (  !(sel_b2)  &&  !(sel_out)  ) |-> out_xor == selected_input_b2 ^ a ;endproperty
assert property (XorSynceotid);

property ValidXorSynceotid; @(posedge clk) (sel_b1) &&  (  !(sel_b2)  &&  !(sel_out)  ) |-> out_xor_inv == ~out_xor ;endproperty
assert property (ValidXorSynceotid);

property ValidXorSynceotid_2; @(posedge clk) (sel_b1) &&  (  !(sel_b2)  &&  !(sel_out)  ) |-> out_logical_inv == !out_xor ;endproperty
assert property (ValidXorSynceotid_2);

property SyncEqeotid_2; @(posedge clk) (  !(sel_b1)  &&  (  !(sel_b2)  &&  (sel_out) ) ) |-> out_always == out_logical_inv ;endproperty
assert property (SyncEqeotid_2);

property SyncEqeotid_3; @(posedge clk) (  !(sel_b1)  &&  (  !(sel_b2)  &&  !(sel_out) ) ) |-> out_always == out_xor_inv ;endproperty
assert property (SyncEqeotid_3);

endmodule