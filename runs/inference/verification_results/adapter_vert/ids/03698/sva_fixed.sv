module top_module_sva (
    input logic binary_input,
    input logic data,
    input logic gray_code_output,
    input logic shift_amount,
    input logic shifted_gray_code_output,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic clk_in_17
);

property ClockSynceotid; @(posedge clk_in_17) (binary_input) |-> (gray_code_output) ;endproperty
assert property (ClockSynceotid);

property ShiftSynceotid; @(posedge clk_in_17) (gray_code_output) &&  (  (shift_amount) == (2'b00)  ) |-> (shifted_gray_code_output) == (data) ;endproperty
assert property (ShiftSynceotid);

property ShiftOneotid; @(posedge clk_in_17) (gray_code_output) &&  (  (shift_amount) == (2'b01)  ) |-> (shifted_gray_code_output) == ({data[2:0], data[3]}) ;endproperty
assert property (ShiftOneotid);

property ShiftTwoeotid; @(posedge clk_in_17) (gray_code_output) &&  (  (shift_amount) == (2'b10)  ) |-> (shifted_gray_code_output) == ({data[1:0], data[3:2]}) ;endproperty
assert property (ShiftTwoeotid);

property ShiftOneeotid; @(posedge clk_in_17) (gray_code_output) &&  (  (shift_amount) != 2'b00 &&  (shift_amount) != 2'b01 &&  (shift_amount) != 2'b10  ) |-> (shifted_gray_code_output) == ({data[0], data[3:1]}) ;endproperty
assert property (ShiftOneeotid);

endmodule