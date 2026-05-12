property ClockSynceotid; @(posedge clk_osc_19) (Y) == ( (A1 & A2) | (VPWR & !VGND & !A1 & A2) | (!VPWR & VGND & A1 & !A2) ) &&  ( !B1_N ) &&  ( !(VGND & VPB & VNB) ) ;endproperty 
 