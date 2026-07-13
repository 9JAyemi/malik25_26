module xor_module_sva (
    input logic a,
    input logic b,
    input logic out_comb_logic,
    input logic clk_in_15,
    input logic err_14
);

property XorSynceotid; @(posedge clk_in_15) (a) != (b) |-> (out_comb_logic) == (a ^ b) ;endproperty
assert property (XorSynceotid);

property SyncEqeotid; @(posedge clk_in_15) (a) == (b) &&  (out_comb_logic) != (a ^ b) |-> err_14 ;endproperty
assert property (SyncEqeotid);

endmodule