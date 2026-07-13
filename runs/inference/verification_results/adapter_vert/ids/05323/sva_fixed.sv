module Counter_sva (
    input logic Clock,
    input logic Count,
    input logic Enable,
    input logic RegEnable,
    input logic RegIn,
    input logic Reset,
    input logic Initial
);

property ResetSynceotid; @(posedge Clock) (Reset) |-> (Count == Initial); endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge Clock) (Enable) && (RegEnable) |-> (Count == RegIn); endproperty
assert property (EnableSynceotid);

property ResetSynceotid_2; @(posedge Clock) (Reset) && !(Enable) && !(RegEnable) |-> (Count == Initial); endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge Clock) (Reset) && !(Enable) && (RegEnable) |-> (Count == RegIn); endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge Clock) (Reset) && (Enable) && !(RegEnable) |-> (Count == Initial); endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(posedge Clock) (Reset) && (Enable) && (RegEnable) |-> (Count == RegIn); endproperty
assert property (ResetSynceotid_5);

endmodule