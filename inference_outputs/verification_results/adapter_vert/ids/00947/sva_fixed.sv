module and_gate_sva (
    input logic in,
    input logic out_and,
    input logic out_or,
    input logic out_xor,
    input logic clk_in_1
);

property AndSynceotid; @(posedge clk_in_1) ( in ) |-> ( out_and ) ; endproperty
assert property (AndSynceotid);

property OrSynceotid; @(posedge clk_in_1) ( in ) |-> ( out_or ) ; endproperty
assert property (OrSynceotid);

property XorSynceotid; @(posedge clk_in_1) ( in ) |-> ( out_xor ) ; endproperty
assert property (XorSynceotid);

endmodule