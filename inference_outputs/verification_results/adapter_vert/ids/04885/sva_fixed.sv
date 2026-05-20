module sky130_fd_sc_ls__o211a_sva (
    input logic A1,
    input logic A2,
    input logic X,
    input logic and0_out_X,
    input logic or0_out,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (X) |-> (or0_out) && (and0_out_X); endproperty
assert property (ClockSynceotid);

property SyncSafeeotid; @(posedge clk_osc_19) (or0_out) &&  (  (A2) || (A1)  ) &&  (  (or0_out) && (and0_out_X)  ) |-> (X) == (and0_out_X); endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk_osc_19) (or0_out) &&  (  (A2) || (A1)  ) &&  (  !(or0_out) || !(and0_out_X)  ) |-> (X) != (and0_out_X); endproperty
assert property (SyncSafeeotid_2);

endmodule