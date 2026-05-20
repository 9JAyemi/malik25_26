module ripple_carry_adder_sva (
    input logic A,
    input logic B,
    input logic COUT,
    input logic SUM,
    input logic b0,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) |-> (SUM) ;endproperty
assert property (AddOneeotid);

property CarrySynceotid; @(posedge clk_in_1) (B) |-> (SUM) ;endproperty
assert property (CarrySynceotid);

property AddOneeotid_2; @(posedge clk_in_1) (A) &&  (B) &&  ( 1'b0 ) |->  (SUM)  &&  (COUT) ;endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (A) &&  (B) &&  (  1'b0  ) |->  (SUM)  &&  (COUT) ;endproperty
assert property (AddOneeotid_3);

property AddOneeotid_4; @(posedge clk_in_1) (A) &&  (  B  ) &&  (  1'b0  ) |->  (SUM)  &&  (COUT) ;endproperty
assert property (AddOneeotid_4);

property AddOneeotid_5; @(posedge clk_in_1) (  A  ) &&  (  B  ) &&  (  1'b0  ) |->  (SUM)  &&  (COUT) ;endproperty
assert property (AddOneeotid_5);

endmodule