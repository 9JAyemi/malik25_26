module xor_gate_sva (
    input logic a,
    input logic b,
    input logic out_comb,
    input logic clk_in_16
);

property XorSynceotid; @(posedge clk_in_16) (a) &&  ( !b ) |->  ( out_comb ) ;endproperty
assert property (XorSynceotid);

property XorSynceotid_2; @(posedge clk_in_16)  ( !a ) &&  ( b ) |->  ( out_comb ) ;endproperty
assert property (XorSynceotid_2);

property XorSynceotid_3; @(posedge clk_in_16) (a) &&  ( b ) |->  ( !out_comb ) ;endproperty
assert property (XorSynceotid_3);

property XorSynceotid_4; @(posedge clk_in_16)  ( !a ) &&  ( !b ) |->  ( !out_comb ) ;endproperty
assert property (XorSynceotid_4);

endmodule