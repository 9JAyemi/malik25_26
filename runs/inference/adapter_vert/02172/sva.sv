property AdderSynceotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (B) |-> (S) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (Cin) |-> (S) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) && (B) && (Cin) |-> (Cout) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) && (B) && ! (Cin) |-> ! (Cout) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) && ! (B) && (Cin) |-> ! (Cout) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) ! (A) && (B) && (Cin) |-> ! (Cout) ;endproperty 
 