module pcidec_new_sva (
    input logic a1,
    input logic ad_i,
    input logic adr,
    input logic adr_o,
    input logic adrcfg_o,
    input logic adrmem_o,
    input logic bar0_i,
    input logic cbe_i,
    input logic cmd,
    input logic cmd_o,
    input logic idsel_i,
    input logic idsel_s,
    input logic memEN_i,
    input logic nrst_i,
    input logic pciadrLD_i,
    input logic b0,
    input logic b00,
    input logic b011,
    input logic b1,
    input logic b101,
    input logic b111,
    input logic b1111_1111_1111_1111_1111_111
);

property ResetSynceotid; @(negedge nrst_i) ( nrst_i ) |-> ( adr ) == ( 23'b1111_1111_1111_1111_1111_111 ) && ( cmd ) == ( 3'b111 ) && ( idsel_s ) == ( 1'b0 ) ;endproperty
assert property (ResetSynceotid);

property SyncLoadeotid; @(negedge nrst_i) ( nrst_i ) &&  (  pciadrLD_i == 1 ) |-> ( adr ) == ( ad_i ) && ( cmd ) == ( cbe_i ) && ( idsel_s ) == ( idsel_i ) ;endproperty
assert property (SyncLoadeotid);

property ValidAccesseotid; @(negedge nrst_i) ( memEN_i == 1'b1 ) &&  (  adr [31:25] == bar0_i ) &&  (  adr [1:0] == 2'b00 ) &&  (  cmd [3:1] == 3'b011 )  |-> ( adrmem_o ) == ( 1'b1 ) ;endproperty
assert property (ValidAccesseotid);

property ValidAccesseotid_2; @(negedge nrst_i) ( idsel_s == 1'b1 ) &&  (  adr [1:0] == 2'b00 ) &&  (  cmd [3:1] == 3'b101 )  |-> ( adrcfg_o ) == ( 1'b1 ) ;endproperty
assert property (ValidAccesseotid_2);

property ValidDataeotid; @(negedge nrst_i) (  cbe_i [3] && cbe_i [2] ) |-> ( a1 ) == ( 1'b0 ) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(negedge nrst_i) (  cbe_i [3] && cbe_i [2] ) |-> ( adr_o ) == ( {adr [24:2], a1} ) ;endproperty
assert property (ValidDataeotid_2);

property ValidCmdseotid; @(negedge nrst_i) (  cbe_i [3] && cbe_i [2] ) |-> ( cmd_o ) == ( cmd ) ;endproperty
assert property (ValidCmdseotid);

endmodule