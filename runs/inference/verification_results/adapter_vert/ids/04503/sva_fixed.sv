module sky130_fd_sc_hd__fah_sva (
    input logic A,
    input logic B,
    input logic CI,
    input logic COUT,
    input logic SUM,
    input logic a_b,
    input logic a_ci,
    input logic b_ci,
    input logic xor0_out_SUM,
    input logic clk_in_18
);

property ClockSynceotid; @(posedge clk_in_18) (COUT) |-> (SUM) ;endproperty
assert property (ClockSynceotid);

property ValidDataeotid; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) |-> (xor0_out_SUM) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) |-> (SUM) ;endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) &&  (  xor0_out_SUM ) |-> (a_b) ;endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) &&  (  xor0_out_SUM ) |-> (a_ci) ;endproperty
assert property (ValidDataeotid_4);

property ValidDataeotid_5; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) &&  (  xor0_out_SUM ) |-> (b_ci) ;endproperty
assert property (ValidDataeotid_5);

property ValidDataeotid_6; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) &&  (  xor0_out_SUM ) &&  (  a_b ) &&  (  a_ci ) &&  (  b_ci ) |-> (COUT) ;endproperty
assert property (ValidDataeotid_6);

endmodule