module l1_data_cache_64entry_4way_line64b_bus_8b_disable_cache_sva (
    input logic b_req_valid,
    input logic iCLOCK,
    input logic iRD_REQ,
    input logic iREMOVE,
    input logic iRESET_SYNC,
    input logic inRESET,
    input logic b0
);

property ResetSynceotid; @(posedge iCLOCK) ( inRESET ) &&  (  !iRESET_SYNC ) &&  (  !iREMOVE ) |-> b_req_valid == 1'b0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge iCLOCK) ( inRESET ) &&  (  iRESET_SYNC ) &&  (  !iREMOVE ) |-> b_req_valid == 1'b0 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge iCLOCK) ( inRESET ) &&  (  !iRESET_SYNC ) &&  (  iREMOVE ) |-> b_req_valid == 1'b0 ;endproperty
assert property (ResetSynceotid_3);

property ValidReqeotid; @(posedge iCLOCK) ( !inRESET ) &&  (  !iRESET_SYNC ) &&  (  !iREMOVE ) |-> b_req_valid == iRD_REQ ;endproperty
assert property (ValidReqeotid);

endmodule