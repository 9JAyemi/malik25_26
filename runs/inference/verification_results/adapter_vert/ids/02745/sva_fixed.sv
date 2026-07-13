module ripple_carry_adder_sva (
    input logic A,
    input logic B,
    input logic CI,
    input logic CO,
    input logic S,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty
assert property (AddOneeotid);

property CarrySynceotid; @(posedge clk_in_1) (B) |-> (S) ;endproperty
assert property (CarrySynceotid);

property CarrySynceotid_2; @(posedge clk_in_1) (CI) |-> (S) ;endproperty
assert property (CarrySynceotid_2);

property AddOneeotid_2; @(posedge clk_in_1) (A) &&  (B) &&  (CI) |-> (CO) ;endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (A) &&  (B) &&  (!CI) |-> !(CO) ;endproperty
assert property (AddOneeotid_3);

property AddOneeotid_4; @(posedge clk_in_1) (A) &&  (!B) &&  (CI) |-> !(CO) ;endproperty
assert property (AddOneeotid_4);

property AddOneeotid_5; @(posedge clk_in_1) (!A) &&  (B) &&  (CI) |-> !(CO) ;endproperty
assert property (AddOneeotid_5);

endmodule