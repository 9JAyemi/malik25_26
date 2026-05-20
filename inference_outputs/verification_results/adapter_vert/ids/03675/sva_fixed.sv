module ternary_add_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic o,
    input logic SIGN_EXT,
    input logic WIDTH,
    input logic clk_in_17
);

property AddSynceotid; @(posedge clk_in_17) ( !SIGN_EXT ) |-> o == a + b + c ; endproperty
assert property (AddSynceotid);

property AddSynceotid_2; @(posedge clk_in_17) ( SIGN_EXT ) |-> o == {a[WIDTH-1],a[WIDTH-1],a} + {b[WIDTH-1],b[WIDTH-1],b} + {c[WIDTH-1],c[WIDTH-1],c} ; endproperty
assert property (AddSynceotid_2);

endmodule