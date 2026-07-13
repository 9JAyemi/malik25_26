property ResetSynceotid; @(posedge Clock) (Reset) |-> (Count == Initial); endproperty 
 
 property EnableSynceotid; @(posedge Clock) (Enable) && (RegEnable) |-> (Count == RegIn); endproperty 
 
 property ResetSynceotid; @(posedge Clock) (Reset) && !(Enable) && !(RegEnable) |-> (Count == Initial); endproperty 
 
 property ResetSynceotid; @(posedge Clock) (Reset) && !(Enable) && (RegEnable) |-> (Count == RegIn); endproperty 
 
 property ResetSynceotid; @(posedge Clock) (Reset) && (Enable) && !(RegEnable) |-> (Count == Initial); endproperty 
 
 property ResetSynceotid; @(posedge Clock) (Reset) && (Enable) && (RegEnable) |-> (Count == RegIn); endproperty 
 
 