property MaxAeotid; @(posedge clk_in_1) (A1) > (A2) |-> (Y) == (A1) ; endproperty 
 
 property MaxBorMaxeotid; @(posedge clk_in_1) (A1) <= (A2) && (B1) > (B2) && (B1) > (Y) |-> (Y) == (B1) ; endproperty 
 
 property MaxCgreaterthanYor; @(posedge clk_in_1) (A1) <= (A2) && (B1) <= (B2) && (C1) > (C2) && (C1) > (Y) |-> (Y) == (C1) ; endproperty 
 
 property MaxDgreaterthanor; @(posedge clk_in_1) (A1) <= (A2) && (B1) <= (B2) && (C1) <= (C2) && (D1) > (D2) && (D1) > (Y) |-> (Y) == (D1) ; endproperty 
 
 property MaxDorMaxDor; @(posedge clk_in_1) (A1) <= (A2) && (B1) <= (B2) && (C1) <= (C2) &&  (D1) <= (D2)  |-> (Y) == (D2) ; endproperty 
 