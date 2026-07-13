property ResetSynceotid; @(posedge iCLOCK) ( inRESET ) &&  (  !iRESET_SYNC ) &&  (  !iREMOVE ) |-> b_req_valid == 1'b0 ;endproperty 
 property ResetSynceotid; @(posedge iCLOCK) ( inRESET ) &&  (  iRESET_SYNC ) &&  (  !iREMOVE ) |-> b_req_valid == 1'b0 ;endproperty 
 property ResetSynceotid; @(posedge iCLOCK) ( inRESET ) &&  (  !iRESET_SYNC ) &&  (  iREMOVE ) |-> b_req_valid == 1'b0 ;endproperty 
 property ValidReqeotid; @(posedge iCLOCK) ( !inRESET ) &&  (  !iRESET_SYNC ) &&  (  !iREMOVE ) |-> b_req_valid == iRD_REQ ;endproperty 
 