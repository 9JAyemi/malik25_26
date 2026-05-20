module axis_infrastructure_v1_1_clock_synchronizer_sva (
    input logic clk,
    input logic synch_d,
    input logic synch_in,
    input logic synch_out,
    input logic C_NUM_STAGES
);

property SyncIneotid; @(posedge clk) (synch_in) |-> (synch_d) ;endproperty
assert property (SyncIneotid);

property SyncFloweotid; @(posedge clk) (synch_in) &&  (  (C_NUM_STAGES)  != 0 ) |-> (synch_d) ;endproperty
assert property (SyncFloweotid);

property SyncFloweotid_2; @(posedge clk) (synch_in) &&  (  (C_NUM_STAGES)  != 0 ) &&  (  (C_NUM_STAGES)  != 1 )  |-> (synch_d) ;endproperty
assert property (SyncFloweotid_2);

property SyncFloweotid_3; @(posedge clk) (synch_in) &&  (  (C_NUM_STAGES)  != 0 ) &&  (  (C_NUM_STAGES)  != 1 ) &&  (  (C_NUM_STAGES)  != 2 )  |-> (synch_out) == (synch_d) ;endproperty
assert property (SyncFloweotid_3);

endmodule