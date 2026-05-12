property ReadSynceotid; @(posedge CLK) (EN_write_0) |-> write_0 == wire_0 ;endproperty 
 
 property WriteSynceotid; @(posedge CLK) (EN_write_1) |-> write_1 == wire_1 ;endproperty 
 
 property WriteSynceotid; @(posedge CLK) (EN_write_2) |-> write_2 == wire_2 ;endproperty 
 
 property SyncReadeotid; @(posedge CLK) (EN_write_0) |-> read_0 == wire_0 ;endproperty 
 
 property SyncWriteeotid; @(posedge CLK) (EN_write_1) |-> read_1 == wire_1 ;endproperty 
 
 property SyncWriteeotid; @(posedge CLK) (EN_write_2) |-> read_2 == wire_2 ;endproperty 
 
 property SyncWriteeotid; @(posedge CLK) (EN_write_0) |-> r == wire_3 ;endproperty 
 
 property SyncWriteeotid; @(posedge CLK) (EN_write_1) |-> r == wire_3 ;endproperty 
 
 property SyncWriteeotid; @(posedge CLK) (EN_write_2) |-> r == wire_3 ;endproperty 
 