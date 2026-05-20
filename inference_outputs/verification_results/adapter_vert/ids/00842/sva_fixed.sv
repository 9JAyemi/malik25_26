module ripple_carry_adder_sva (
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum,
    input logic clk_in_14
);

property AddOneeotid; @(posedge clk_in_14) (a) |-> (sum) ;endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_14) (b) |-> (sum) ;endproperty
assert property (AddOneeotid_2);

property CarrySynceotid; @(posedge clk_in_14) (a) &&  (b) &&  (  !cin ) |->  (sum) ;endproperty
assert property (CarrySynceotid);

property CarrySynceotid_2; @(posedge clk_in_14) (a) &&  (  !b ) &&  (  !cin ) |->  (sum) ;endproperty
assert property (CarrySynceotid_2);

property CarrySynceotid_3; @(posedge clk_in_14) (  !a ) &&  (b) &&  (  !cin ) |->  (sum) ;endproperty
assert property (CarrySynceotid_3);

property CarrySynceotid_4; @(posedge clk_in_14) (  !a ) &&  (  !b ) &&  (  !cin ) |->  (sum) ;endproperty
assert property (CarrySynceotid_4);

property CarrySynceotid_5; @(posedge clk_in_14) (a) &&  (b) &&  (  !cin ) |->  (cout) ;endproperty
assert property (CarrySynceotid_5);

property CarrySynceotid_6; @(posedge clk_in_14) (a) &&  (  !b ) &&  (  !cin ) |->  (cout) ;endproperty
assert property (CarrySynceotid_6);

property CarrySynceotid_7; @(posedge clk_in_14) (  !a ) &&  (b) &&  (  !cin ) |->  (cout) ;endproperty
assert property (CarrySynceotid_7);

property CarrySynceotid_8; @(posedge clk_in_14) (  !a ) &&  (  !b ) &&  (  !cin ) |->  (cout) ;endproperty
assert property (CarrySynceotid_8);

endmodule