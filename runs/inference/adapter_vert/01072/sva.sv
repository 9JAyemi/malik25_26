property AdderSynceotid; @(posedge clk_in_1) (A) |-> (S) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (C_out) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (!Cin) |-> (C_out) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (!B) &&  (Cin) |-> (C_out) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (!B) &&  (!Cin) |-> (S) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (B) &&  (Cin) |-> (C_out) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (B) &&  (!Cin) |-> (S) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (!A) &&  (!B) &&  (Cin) |-> (C_out) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1)  (A) &&  (B)  &&  (Cin)  &&  (  !S  &&  !C_out ) |->  (  !A  || !B  || !Cin )  ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1)  (A) &&  (B)  &&  (!Cin)  &&  (  !S  &&  C_out ) |->  (  !A  || !B  || Cin )  ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1)  (A) &&  (!B)  &&  (Cin)  &&  (  S  &&  !C_out ) |->  (  !A  || B  || !Cin )  ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1)  (A) &&  (!B)  &&  (!Cin)  &&  (  S  &&  C_out ) |->  (  A  &&  !B  &&  !Cin )  ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1)  (!A) &&  (B)  &&  (Cin)  &&  (  !S  &&  C_out ) |->  (  A  || !B  || !Cin )  ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1)  (!A) &&  (B)  &&  (!Cin)  &&  (  S  &&  !C_out ) |->  (  A  || !B  &&  !Cin )  ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1)  (!A) &&  (!B)  &&  (Cin)  &&  (  !S  &&  C_out ) |->  (  A  || B  || !Cin )  ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1)  (A) &&  (B)  &&  (Cin)  &&  (  S  &&  C_out ) |->  (  !A  && !B  && !Cin )  ; endproperty 
 