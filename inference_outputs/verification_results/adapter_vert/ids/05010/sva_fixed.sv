module sky130_fd_sc_lp__and4_sva (
    input logic X,
    input logic and0_out_X,
    input logic clk_in_15
);

property SyncIneotid; @(posedge clk_in_15) (X) |-> (and0_out_X) ;endproperty
assert property (SyncIneotid);

property ValidIneotid; @(posedge clk_in_15) (and0_out_X) |-> (X) ;endproperty
assert property (ValidIneotid);

endmodule