module sky130_fd_sc_lp__a32o_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic VGND,
    input logic VNB,
    input logic VPB,
    input logic VPWR,
    input logic X,
    input logic clock_div_17
);

property ClockSafeeotid; @(posedge clock_div_17) (A1) &&  ( !A2 ) &&  ( !A3 ) &&  ( !B1 ) &&  ( !B2 ) &&  ( !VPWR ) &&  ( !VGND ) &&  ( !VPB ) &&  ( !VNB ) |-> (X) ;endproperty
assert property (ClockSafeeotid);

property ClockSafeeotid_2; @(posedge clock_div_17) (A1) &&  (  A2 ) &&  (  A3 ) &&  (  B1 ) &&  (  B2 ) &&  (  VPWR ) &&  (  VGND ) &&  (  VPB ) &&  (  VNB ) |-> !(X) ;endproperty
assert property (ClockSafeeotid_2);

endmodule