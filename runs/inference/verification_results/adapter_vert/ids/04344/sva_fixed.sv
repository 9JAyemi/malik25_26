module digital_circuit_sva (
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VGND,
    input logic VNB,
    input logic VPB,
    input logic VPWR,
    input logic Y,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (Y) == ( (A1 & A2) | (VPWR & !VGND & !A1 & A2) | (!VPWR & VGND & A1 & !A2) ) &&  ( !B1_N ) &&  ( !(VGND & VPB & VNB) ) ;endproperty
assert property (ClockSynceotid);

endmodule