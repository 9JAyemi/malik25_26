property ClockSynceotid; @(posedge clk) (sel) |-> (mux_out) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (sel) == ( 0 ) |-> (out_mux) == (  data0  ) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (sel) == ( 1 ) |-> (out_mux) == (  data1  ) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (sel) == ( 2 ) |-> (out_mux) == (  data2  ) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (sel) == ( 3 ) |-> (out_mux) == (  data3  ) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (sel) == ( 4 ) |-> (out_mux) == (  data4  ) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (sel) == ( 5 ) |-> (out_mux) == (  data5  ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) == ( 0 ) &&  (  data0  != 0  &&  data0  != 1  &&  data0  != 2  &&  data0  != 3  &&  data0  != 4  &&  data0  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 0  &&  (  data1  != 0  &&  data1  != 1  &&  data1  != 2  &&  data1  != 3  &&  data1  != 4  &&  data1  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 1  &&  (  data2  != 0  &&  data2  != 1  &&  data2  != 2  &&  data2  != 3  &&  data2  != 4  &&  data2  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 2  &&  (  data3  != 0  &&  data3  != 1  &&  data3  != 2  &&  data3  != 3  &&  data3  != 4  &&  data3  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 3  &&  (  data4  != 0  &&  data4  != 1  &&  data4  != 2  &&  data4  != 3  &&  data4  != 4  &&  data4  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 4  &&  (  data5  != 0  &&  data5  != 1  &&  data5  != 2  &&  data5  != 3  &&  data5  != 4  &&  data5  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 5  &&  (  data0  != 0  &&  data0  != 1  &&  data0  != 2  &&  data0  != 3  &&  data0  != 4  &&  data0  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 5  &&  (  data1  != 0  &&  data1  != 1  &&  data1  != 2  &&  data1  != 3  &&  data1  != 4  &&  data1  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 5  &&  (  data2  != 0  &&  data2  != 1  &&  data2  != 2  &&  data2  != 3  &&  data2  != 4  &&  data2  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 5  &&  (  data3  != 0  &&  data3  != 1  &&  data3  != 2  &&  data3  != 3  &&  data3  != 4  &&  data3  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 5  &&  (  data4  != 0  &&  data4  != 1  &&  data4  != 2  &&  data4  != 3  &&  data4  != 4  &&  data4  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 5  &&  (  data5  != 0  &&  data5  != 1  &&  data5  != 2  &&  data5  != 3  &&  data5  != 4  &&  data5  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 5  &&  (  data0  != 0  &&  data0  != 1  &&  data0  != 2  &&  data0  != 3  &&  data0  != 4  &&  data0  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sel) != 5 