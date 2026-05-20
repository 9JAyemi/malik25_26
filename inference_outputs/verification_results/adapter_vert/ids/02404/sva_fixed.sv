module mux_dff_sva (
    input logic D,
    input logic buf_mux_out,
    input logic in_0,
    input logic in_1,
    input logic mux_out,
    input logic sel_0,
    input logic sel_1,
    input logic b0,
    input logic clk_osc_15
);

property ClockSynceotid; @(posedge clk_osc_15) (D) |-> (buf_mux_out) ;endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_osc_15) (D) &&  (  (sel_0) &&  (sel_1)  ) |-> (mux_out) == (in_0) ;endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_osc_15) (D) &&  (  (sel_0) && !(sel_1)  ) |-> (mux_out) == (in_1) ;endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_osc_15) (D) &&  (  !(sel_0)  &&  (sel_1)  ) |-> (mux_out) == 1'b0 ;endproperty
assert property (SyncIneotid_3);

endmodule