module simple_calculator_sva (
    input logic a,
    input logic add_out,
    input logic b,
    input logic div_out,
    input logic mul_out,
    input logic op,
    input logic sub_out,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (op) == (2'b00) |-> add_out == a + b && sub_out == 0 && mul_out == 0 && div_out == 0 ; endproperty
assert property (AddSynceotid);

property SubSynceotid; @(posedge clk_in_1) (op) == (2'b01) |-> add_out == 0 && sub_out == a - b && mul_out == 0 && div_out == 0 ; endproperty
assert property (SubSynceotid);

property MultSynceotid; @(posedge clk_in_1) (op) == (2'b10) |-> add_out == 0 && sub_out == 0 && mul_out == a * b && div_out == 0 ; endproperty
assert property (MultSynceotid);

property DivSynceotid; @(posedge clk_in_1) (op) == (2'b11) |-> add_out == 0 && sub_out == 0 && mul_out == 0 && div_out == a / b ; endproperty
assert property (DivSynceotid);

endmodule