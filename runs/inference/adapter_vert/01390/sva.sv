property AdderSynceotid; @(posedge clk_in_17) (A) |-> (S) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_17) (A) &&  (B) &&  (Cin) |->  (Cout) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_17) (A) &&  (B) &&  (!Cin) |->  (Cout) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_17) (A) &&  (!B) &&  (Cin) |->  (Cout) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_17) (A) &&  (!B) &&  (!Cin) |->  (Cout) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_17) (A) ||  (B) ||  (Cin) |->  (S) ;endproperty 
 
 property SyncAddereotid; @(posedge clk_in_17) (A) ||  (B) ||  (Cin) &&  (  ! (A)  || ! (B)  ||  (Cout) ) |->  (S) ;endproperty 
 
 property SyncAddereotid; @(posedge clk_in_17) (A) ||  (B) ||  (Cin) &&  (  ! (A)  || ! (B)  ||  (Cout) ) &&  (  ! (A)  ||  (B)  ||  (Cout) ) |->  (S) ;endproperty 
 
 property yncAddereotid; @(posedge clk_in_17) (A) ||  (B) ||  (Cin) &&  (  ! (A)  || ! (B)  ||  (Cout) ) &&  (  ! (A)  ||  (B)  ||  (Cout) ) &&  (  (A)  &&  (B)  &&  (Cin)  ||  (  ! (A)  && ! (B)  &&  (Cout)  ) ) |->  (S) ;endproperty 
 