property ResetSynceotid; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> prev_count_clk == 0 ;endproperty 
 
 property SyncLockeotid; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |->  (prev_pos11 == pos11) && (prev_pos12 == pos12) && (prev_pos21 == pos21) && (prev_pos22 == pos22) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (clear != 2'b10) && (clear != 2'b11)  |->  (prev_pos11 == pos11 + 1) && (prev_pos12 == pos12 + 1) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (clear != 2'b10) && (clear != 2'b11) && (m1 != 1'b1)  |->  (prev_pos11 == pos11 - 1) && (prev_pos12 == pos12 - 1) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (clear != 2'b10) && (clear != 2'b11)  |->  (prev_pos21 == pos21 + 1) && (prev_pos22 == pos22 + 1) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (clear != 2'b10) && (clear != 2'b11) && (m2 != 1'b1)  |->  (prev_pos21 == pos21 - 1) && (prev_pos22 == pos22 - 1) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> pos_diff_x == 0 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> pos_diff_y == 0 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> count_clk == 0 ;endproperty 
 