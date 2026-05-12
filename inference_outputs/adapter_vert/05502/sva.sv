property PowerOnCheckeotid; @(posedge clk_signal_18) (A1) && (A2) && (A3) |-> (VPWR) && !(VGND) && (VPB) && !(VNB) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_signal_18) (A1) && (A2) && (A3) || (A1) && (A2) && (B1) || (A1) && (A2) && (C1) || (A1) && (A3) && (B1) || (A1) && (A3) && (C1) || (A2) && (A3) && (B1) || (A2) && (A3) && (C1) || (A2) && (B1) && (C1) || (A3) && (B1) && (C1)  == 1'b1 ;endproperty 
 