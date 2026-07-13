module four_to_one_sva (
    input logic input1,
    input logic input2,
    input logic input3,
    input logic input4,
    input logic output1,
    input logic clk_in_1
);

property ValidInputeotid; @(posedge clk_in_1) (input1) |-> (output1) ; endproperty
assert property (ValidInputeotid);

property ValidInputeotid_2; @(posedge clk_in_1) (input2) |-> (output1) ; endproperty
assert property (ValidInputeotid_2);

property ValidInputeotid_3; @(posedge clk_in_1) (input3) |-> (output1) ; endproperty
assert property (ValidInputeotid_3);

property ValidInputeotid_4; @(posedge clk_in_1) (input4) |-> (output1) ; endproperty
assert property (ValidInputeotid_4);

property ValidInputeotid_5; @(posedge clk_in_1) (input1) && @(posedge clk_in_1) (input2) && @(posedge clk_in_1) (input3) && @(posedge clk_in_1) (input4) |-> (output1) ; endproperty
assert property (ValidInputeotid_5);

property ValidInputeotid_6; @(posedge clk_in_1) (input1) || @(posedge clk_in_1) (input2) || @(posedge clk_in_1) (input3) || @(posedge clk_in_1) (input4) |-> (output1) ; endproperty
assert property (ValidInputeotid_6);

endmodule