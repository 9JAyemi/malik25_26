property AdderSynceotid; @(posedge clk_in_1) (A) |-> (S) == (A + B + CIN); endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (CIN) |-> (COUT) == 6'b000010 ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (!CIN) |-> (COUT) == 6'b000001 ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (!B) &&  (CIN) |-> (COUT) == 6'b000010 ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (!B) &&  (!CIN) |-> (COUT) == 6'b000000 ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (B) &&  (CIN) |-> (COUT) == 6'b000010 ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (B) &&  (!CIN) |-> (COUT) == 6'b000001 ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (!B) &&  (CIN) |-> (COUT) == 6'b000010 ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (!B) &&  (!CIN) |-> (COUT) == 6'b000000 ; endproperty 
 