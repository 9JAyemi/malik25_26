property CarryOn; @(posedge clk_in_1) (a) |-> (sig_fa_0_a) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (b) |-> (sig_fa_0_b) ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (ci) |-> (sig_fa_0_ci) ; endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (co) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (s) ; endproperty 
 
 property SyncAddereotid; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty 
 
 property SyncAddereotid; @(posedge clk_in_1) (c) |-> (co) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (c) |-> (s) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (a) |-> (sig_fa_1_a) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (b) |-> (sig_fa_1_b) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (sig_fa_1_ci) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_1_co) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_1_s) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (sig_fa_2) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (sig_fa_2) |-> (co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (sig_fa_2) |-> (s) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) |-> (sig_fa_3_a) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (b) |-> (sig_fa_3_b) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (sig_fa_3_ci) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_3_co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_3_s) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (c) |-> (co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (s) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (a) |-> (sig_fa_4_a) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (b) |-> (sig_fa_4_b) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (sig_fa_4_ci) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_4_co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_4_s) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (c) |-> (co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (s) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (a) |-> (sig_fa_5_a) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (b) |-> (sig_fa_5_b) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (sig_fa_5_ci) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_5_co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_5_s) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (c) |-> (co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (s) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (a) |-> (sig_fa_6_a) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (b) |-> (sig_fa_6_b) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (sig_fa_6_ci) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_6_co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_6_s) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (c) |-> (co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (s) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (a) |-> (sig_fa_7_a) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (b) |-> (sig_fa_7_b) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (sig_fa_7_ci) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_7_co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) &&  (b) &&  (ci) |-> (sig_fa_7_s) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (a) ||  (b) ||  (ci) |-> (c) ; endproperty 
 
 property yncCheckeotid; @(posedge clk_in_1) (c) |-> (co) ; endproperty 
 
 property ncCheckeotid; @(posedge clk_in_1) (c) |-> (s) ; endproperty 
 
 