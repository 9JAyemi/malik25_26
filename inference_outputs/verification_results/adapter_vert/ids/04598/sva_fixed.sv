module adder4_sva (
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (a) |-> (sum) ;endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (b) |-> (sum) ;endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (cin) |-> (sum) ;endproperty
assert property (AddOneeotid_3);

property AddOneeotid_4; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |-> (cout) ;endproperty
assert property (AddOneeotid_4);

property AddOneeotid_5; @(posedge clk_in_1) (a) &&  (b) &&  (!cin) |-> !(cout) ;endproperty
assert property (AddOneeotid_5);

property AddOneeotid_6; @(posedge clk_in_1) (a) &&  (!b) &&  (cin) |-> !(cout) ;endproperty
assert property (AddOneeotid_6);

property AddOneeotid_7; @(posedge clk_in_1) (!a) &&  (b) &&  (cin) |-> !(cout) ;endproperty
assert property (AddOneeotid_7);

property AddOneeotid_8; @(posedge clk_in_1) (a) &&  (!b) &&  (!cin) |-> (cout) ;endproperty
assert property (AddOneeotid_8);

property AddOneeotid_9; @(posedge clk_in_1) (!a) &&  (b) &&  (!cin) |-> (cout) ;endproperty
assert property (AddOneeotid_9);

property AddOneeotid_10; @(posedge clk_in_1) (!a) &&  (!b) &&  (cin) |-> (cout) ;endproperty
assert property (AddOneeotid_10);

property AddOneeotid_11; @(posedge clk_in_1)  (a) &&  (b)  &&  (cin)  ||  (a) &&  (b)  &&  (!cin)  ||  (a) &&  (!b)  &&  (cin)  ||  (!a) &&  (b)  &&  (cin)  &&  (  !a  &&  !b  &&  !cin  ||  a  &&  b  &&  cin  ) ;endproperty
assert property (AddOneeotid_11);

endmodule