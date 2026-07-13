module ripple_carry_adder_sva (
    input logic A,
    input logic B,
    input logic CARRY_IN,
    input logic CARRY_OUT,
    input logic SUM,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) |-> (SUM) ; endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (B) |-> (SUM) ; endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (A) &&  (B) &&  (  !CARRY_IN ) |->  (SUM)  &&  (  !CARRY_OUT ) ; endproperty
assert property (AddOneeotid_3);

property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (  CARRY_IN ) ||  (  !A ) &&  (B) &&  (  !CARRY_IN ) ||  (  A ) &&  (  !B ) &&  (  CARRY_IN ) == (  CARRY_OUT ) ; endproperty
assert property (CarrySynceotid);

endmodule