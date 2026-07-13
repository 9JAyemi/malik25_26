module EHRU_3_sva (
    input logic CLK,
    input logic EN_write_0,
    input logic EN_write_1,
    input logic EN_write_2,
    input logic r,
    input logic read_0,
    input logic read_1,
    input logic read_2,
    input logic wire_0,
    input logic wire_1,
    input logic wire_2,
    input logic wire_3,
    input logic write_0,
    input logic write_1,
    input logic write_2
);

property ReadSynceotid; @(posedge CLK) (EN_write_0) |-> write_0 == wire_0 ;endproperty
assert property (ReadSynceotid);

property WriteSynceotid; @(posedge CLK) (EN_write_1) |-> write_1 == wire_1 ;endproperty
assert property (WriteSynceotid);

property WriteSynceotid_2; @(posedge CLK) (EN_write_2) |-> write_2 == wire_2 ;endproperty
assert property (WriteSynceotid_2);

property SyncReadeotid; @(posedge CLK) (EN_write_0) |-> read_0 == wire_0 ;endproperty
assert property (SyncReadeotid);

property SyncWriteeotid; @(posedge CLK) (EN_write_1) |-> read_1 == wire_1 ;endproperty
assert property (SyncWriteeotid);

property SyncWriteeotid_2; @(posedge CLK) (EN_write_2) |-> read_2 == wire_2 ;endproperty
assert property (SyncWriteeotid_2);

property SyncWriteeotid_3; @(posedge CLK) (EN_write_0) |-> r == wire_3 ;endproperty
assert property (SyncWriteeotid_3);

property SyncWriteeotid_4; @(posedge CLK) (EN_write_1) |-> r == wire_3 ;endproperty
assert property (SyncWriteeotid_4);

property SyncWriteeotid_5; @(posedge CLK) (EN_write_2) |-> r == wire_3 ;endproperty
assert property (SyncWriteeotid_5);

endmodule