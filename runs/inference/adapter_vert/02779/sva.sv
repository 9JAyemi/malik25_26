property ClockSafeeotid; @(posedge clock_div_17) (A1) &&  ( !A2 ) &&  ( !A3 ) &&  ( !B1 ) &&  ( !B2 ) &&  ( !VPWR ) &&  ( !VGND ) &&  ( !VPB ) &&  ( !VNB ) |-> (X) ;endproperty 
 
 property ClockSafeeotid; @(posedge clock_div_17) (A1) &&  (  A2 ) &&  (  A3 ) &&  (  B1 ) &&  (  B2 ) &&  (  VPWR ) &&  (  VGND ) &&  (  VPB ) &&  (  VNB ) |-> !(X) ;endproperty 
 