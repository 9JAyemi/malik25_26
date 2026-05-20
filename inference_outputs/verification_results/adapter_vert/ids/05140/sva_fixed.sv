module four_bit_adder_sva (
    input logic A,
    input logic B,
    input logic CI,
    input logic S,
    input logic carry_out,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (B) |-> (S) ;endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (CI) |-> (S) ;endproperty
assert property (AddOneeotid_3);

property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (CI) |-> (carry_out) ;endproperty
assert property (CarrySynceotid);

property CarrySynceotid_2; @(posedge clk_in_1) (A) &&  (B) &&  (!CI) |-> (carry_out) ;endproperty
assert property (CarrySynceotid_2);

property CarrySynceotid_3; @(posedge clk_in_1) (A) &&  (!B) &&  (CI) |-> (carry_out) ;endproperty
assert property (CarrySynceotid_3);

property CarrySynceotid_4; @(posedge clk_in_1) (A) &&  (!B) &&  (!CI) |->  (S)  &&  ( !carry_out) ;endproperty
assert property (CarrySynceotid_4);

property CarrySynceotid_5; @(posedge clk_in_1) (!A) &&  (B) &&  (CI) |->  (S)  &&  ( !carry_out) ;endproperty
assert property (CarrySynceotid_5);

property CarrySynceotid_6; @(posedge clk_in_1) (!A) &&  (B) &&  (!CI) |-> (carry_out) ;endproperty
assert property (CarrySynceotid_6);

property CarrySynceotid_7; @(posedge clk_in_1) (!A) &&  (!B) &&  (CI) |->  (S)  &&  ( !carry_out) ;endproperty
assert property (CarrySynceotid_7);

property CarrySynceotid_8; @(posedge clk_in_1) (!A) &&  (!B) &&  (!CI) |->  (S)  &&  ( !carry_out) ;endproperty
assert property (CarrySynceotid_8);

endmodule