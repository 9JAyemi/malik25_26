module mdc_mdio_sva (
    input logic current_state,
    input logic data_counter,
    input logic data_in,
    input logic data_in_r,
    input logic duplex_mode,
    input logic mdio_in_w,
    input logic mdio_mdc,
    input logic next_state,
    input logic preamble,
    input logic speed_select,
    input logic ACQUIRE,
    input logic IDLE,
    input logic PHY_AD,
    input logic b0,
    input logic b10,
    input logic h11,
    input logic h1f
);

property SyncIneotid; @(posedge mdio_mdc) ( current_state ) == ( IDLE ) &&  (  preamble == 1 && mdio_in_w == 0 ) |-> ( next_state ) == ( ACQUIRE ) ;endproperty
assert property (SyncIneotid);

property SyncDataeotid; @(posedge mdio_mdc) ( current_state ) == ( IDLE ) &&  (  !(  preamble == 1 && mdio_in_w == 0 )  ) |-> ( next_state ) == ( IDLE ) ;endproperty
assert property (SyncDataeotid);

property SyncDataeotid_2; @(posedge mdio_mdc) ( current_state ) == ( ACQUIRE ) &&  (  data_counter == 6'h1f ) |-> ( next_state ) == ( IDLE ) ;endproperty
assert property (SyncDataeotid_2);

property SyncDataeotid_3; @(posedge mdio_mdc) ( current_state ) == ( ACQUIRE ) &&  (  data_counter != 6'h1f ) |-> ( next_state ) == ( ACQUIRE ) ;endproperty
assert property (SyncDataeotid_3);

property SyncDataeotid_4; @(posedge mdio_mdc) ( data_counter ) == ( 6'h1f ) &&  (  data_in[31] == 1'b0 && data_in[29:28]==2'b10 && data_in[27:23] == PHY_AD && data_in[22:18] == 5'h11 ) |-> ( speed_select ) == ( data_in_r[16:15] ) &&  (  duplex_mode  == data_in_r[14] ) ;endproperty
assert property (SyncDataeotid_4);

endmodule