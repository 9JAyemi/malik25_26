module magnitude_comparator_selector_sva (
    input logic a,
    input logic b,
    input logic comparison_result,
    input logic input_selected,
    input logic select,
    input logic b00,
    input logic b01,
    input logic clk_in_1
);

property GreaterThaneotid; @(posedge clk_in_1) (a) > (b) |-> comparison_result == a && input_selected == 2'b00 ;endproperty
assert property (GreaterThaneotid);

property GreaterThaneotid_2; @(posedge clk_in_1) (b) > (a) |-> comparison_result == b && input_selected == 2'b01 ;endproperty
assert property (GreaterThaneotid_2);

property Equalizeeotid; @(posedge clk_in_1) (a) == (b)  |-> comparison_result == a && input_selected == select; endproperty
assert property (Equalizeeotid);

endmodule