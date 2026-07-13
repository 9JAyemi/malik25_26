property DataSynceotid; @(posedge clk_in_1) (sel_mux1) == (3'b000) |-> (mux1_out) == (data0_mux1) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux1) == (3'b001) |-> (mux1_out) == (data1_mux1) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux1) == (3'b010) |-> (mux1_out) == (data2_mux1) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux1) == (3'b011) |-> (mux1_out) == (data3_mux1) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux1) == (3'b100) |-> (mux1_out) == (data4_mux1) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux1) == (3'b101) |-> (mux1_out) == (data5_mux1) ; endproperty 
 
 property SyncDataeotid; @(posedge clk_in_1) (sel_mux1) != 3'b000 && (sel_mux1) != 3'b001 && (sel_mux1) != 3'b010 && (sel_mux1) != 3'b011 && (sel_mux1) != 3'b100 && (sel_mux1) != 3'b101  |-> (mux1_out) == 4'b0000; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux2) == (3'b000) |-> (mux2_out) == (data0_mux2) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux2) == (3'b001) |-> (mux2_out) == (data1_mux2) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux2) == (3'b010) |-> (mux2_out) == (data2_mux2) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux2) == (3'b011) |-> (mux2_out) == (data3_mux2) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux2) == (3'b100) |-> (mux2_out) == (data4_mux2) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (sel_mux2) == (3'b101) |-> (mux2_out) == (data5_mux2) ; endproperty 
 
 property SyncDataeotid; @(posedge clk_in_1) (sel_mux2) != 3'b000 && (sel_mux2) != 3'b001 && (sel_mux2) != 3'b010 && (sel_mux2) != 3'b011 && (sel_mux2) != 3'b100 && (sel_mux2) != 3'b101  |-> (mux2_out) == 4'b0000; endproperty 
 
 property SyncAddereotid; @(posedge clk_in_1) (mux1_out) and @(posedge clk_in_1) (mux2_out) |-> (out) == (mux1_out + mux2_out) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (sel_mux) == (1'b0) |-> (mux_sel) == (sel_mux1) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (sel_mux) != 1'b0  |-> (mux_sel) == (sel_mux2) ; endproperty 
 