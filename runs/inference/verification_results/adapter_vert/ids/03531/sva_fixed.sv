module and_with_en_sva (
    input logic en,
    input logic in1,
    input logic in2,
    input logic out,
    input logic out_valid,
    input logic clk_enable_19
);

property ValidOnEnableeotid; @(posedge clk_enable_19) (in1) && (in2) |-> (out) ;endproperty
assert property (ValidOnEnableeotid);

property ValidOnEnableeotid_2; @(posedge clk_enable_19) (in1) && (in2) &&  (en) |-> (out_valid) ;endproperty
assert property (ValidOnEnableeotid_2);

endmodule