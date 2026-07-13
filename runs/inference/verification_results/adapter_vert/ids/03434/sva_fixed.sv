module top_module_sva (
    input logic clk,
    input logic data0,
    input logic data1,
    input logic data2,
    input logic data3,
    input logic data4,
    input logic data5,
    input logic mux_out,
    input logic o0,
    input logic o1,
    input logic o2,
    input logic out_3bit,
    input logic out_mux,
    input logic sel
);

property ClockSynceotid; @(posedge clk) (sel) |-> (mux_out) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (sel) == ( 0 ) |-> (out_mux) == (  data0  ) ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk) (sel) == ( 1 ) |-> (out_mux) == (  data1  ) ;endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk) (sel) == ( 2 ) |-> (out_mux) == (  data2  ) ;endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge clk) (sel) == ( 3 ) |-> (out_mux) == (  data3  ) ;endproperty
assert property (ClockSynceotid_5);

property ClockSynceotid_6; @(posedge clk) (sel) == ( 4 ) |-> (out_mux) == (  data4  ) ;endproperty
assert property (ClockSynceotid_6);

property ClockSynceotid_7; @(posedge clk) (sel) == ( 5 ) |-> (out_mux) == (  data5  ) ;endproperty
assert property (ClockSynceotid_7);

property SyncCheckeotid; @(posedge clk) (sel) == ( 0 ) &&  (  data0  != 0  &&  data0  != 1  &&  data0  != 2  &&  data0  != 3  &&  data0  != 4  &&  data0  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (sel) != 0  &&  (  data1  != 0  &&  data1  != 1  &&  data1  != 2  &&  data1  != 3  &&  data1  != 4  &&  data1  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk) (sel) != 1  &&  (  data2  != 0  &&  data2  != 1  &&  data2  != 2  &&  data2  != 3  &&  data2  != 4  &&  data2  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk) (sel) != 2  &&  (  data3  != 0  &&  data3  != 1  &&  data3  != 2  &&  data3  != 3  &&  data3  != 4  &&  data3  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_4);

property SyncCheckeotid_5; @(posedge clk) (sel) != 3  &&  (  data4  != 0  &&  data4  != 1  &&  data4  != 2  &&  data4  != 3  &&  data4  != 4  &&  data4  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_5);

property SyncCheckeotid_6; @(posedge clk) (sel) != 4  &&  (  data5  != 0  &&  data5  != 1  &&  data5  != 2  &&  data5  != 3  &&  data5  != 4  &&  data5  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_6);

property SyncCheckeotid_7; @(posedge clk) (sel) != 5  &&  (  data0  != 0  &&  data0  != 1  &&  data0  != 2  &&  data0  != 3  &&  data0  != 4  &&  data0  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_7);

property SyncCheckeotid_8; @(posedge clk) (sel) != 5  &&  (  data1  != 0  &&  data1  != 1  &&  data1  != 2  &&  data1  != 3  &&  data1  != 4  &&  data1  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_8);

property SyncCheckeotid_9; @(posedge clk) (sel) != 5  &&  (  data2  != 0  &&  data2  != 1  &&  data2  != 2  &&  data2  != 3  &&  data2  != 4  &&  data2  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_9);

property SyncCheckeotid_10; @(posedge clk) (sel) != 5  &&  (  data3  != 0  &&  data3  != 1  &&  data3  != 2  &&  data3  != 3  &&  data3  != 4  &&  data3  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_10);

property SyncCheckeotid_11; @(posedge clk) (sel) != 5  &&  (  data4  != 0  &&  data4  != 1  &&  data4  != 2  &&  data4  != 3  &&  data4  != 4  &&  data4  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_11);

property SyncCheckeotid_12; @(posedge clk) (sel) != 5  &&  (  data5  != 0  &&  data5  != 1  &&  data5  != 2  &&  data5  != 3  &&  data5  != 4  &&  data5  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_12);

property SyncCheckeotid_13; @(posedge clk) (sel) != 5  &&  (  data0  != 0  &&  data0  != 1  &&  data0  != 2  &&  data0  != 3  &&  data0  != 4  &&  data0  != 5 ) |-> (out_3bit) == (  sel ) &&  (  o2 ) == (  sel[2] ) &&  (  o1 ) == (  sel[1] ) &&  (  o0 ) == (  sel[0] ) ;endproperty
assert property (SyncCheckeotid_13);

endmodule