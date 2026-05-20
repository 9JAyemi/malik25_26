module sky130_fd_sc_lp__or2_sva (
    input logic A,
    input logic B,
    input logic X,
    input logic or0_out_X,
    input logic clk_osc_19
);

property ORSynceotid; @(posedge clk_osc_19) (X) |-> (or0_out_X == B) && (or0_out_X == A) ;endproperty
assert property (ORSynceotid);

property ORSynceotid_2; @(posedge clk_osc_19) (or0_out_X) == (B) &&  (A) |-> (X) == (or0_out_X) ;endproperty
assert property (ORSynceotid_2);

endmodule