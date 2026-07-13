property AddOneeotid; @(posedge clk_in_1) (A) |-> (SUM) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (B) |-> (SUM) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (CIN) |-> (SUM) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (CIN) |->  (COUT) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) |->  (COUT) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (CIN) |->  (COUT) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) ||  (B) ||  (CIN) |->  (SUM) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) |->  (  !SUM ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) ||  (  !B  ) ||  (  !CIN  ) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (SUM) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) ||  (B) ||  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (SUM) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) ||  (B) ||  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (