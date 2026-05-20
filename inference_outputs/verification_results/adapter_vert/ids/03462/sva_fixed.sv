module oh_mux8_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic in6,
    input logic in7,
    input logic out,
    input logic sel0,
    input logic sel1,
    input logic sel2,
    input logic sel3,
    input logic sel4,
    input logic sel5,
    input logic sel6,
    input logic sel7,
    input logic clk_in_1
);

property ValidDataeotid; @(posedge clk_in_1) (sel7) |-> (out) == (in7); endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (sel6) |-> (out) == (in6); endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_1) (sel5) |-> (out) == (in5); endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_1) (sel4) |-> (out) == (in4); endproperty
assert property (ValidDataeotid_4);

property ValidDataeotid_5; @(posedge clk_in_1) (sel3) |-> (out) == (in3); endproperty
assert property (ValidDataeotid_5);

property ValidDataeotid_6; @(posedge clk_in_1) (sel2) |-> (out) == (in2); endproperty
assert property (ValidDataeotid_6);

property ValidDataeotid_7; @(posedge clk_in_1) (sel1) |-> (out) == (in1); endproperty
assert property (ValidDataeotid_7);

property ValidDataeotid_8; @(posedge clk_in_1) (sel0) |-> (out) == (in0); endproperty
assert property (ValidDataeotid_8);

endmodule