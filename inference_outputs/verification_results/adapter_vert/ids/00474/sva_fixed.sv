module XOR_M_sva (
    input logic Sgn_Info,
    input logic Sgn_X,
    input logic Sgn_Y,
    input logic cfg_14,
    input logic clk_in_19
);

property SyncXorCheckeotid; @(posedge clk_in_19) ( Sgn_X ) != ( Sgn_Y ) |-> ( Sgn_Info ) == ( Sgn_X ^ Sgn_Y );endproperty
assert property (SyncXorCheckeotid);

property SyncXorCheckeotid_2; @(posedge clk_in_19) ( Sgn_X ) != ( Sgn_Y ) &&  (  !cfg_14 ) |-> ( Sgn_Info ) == ( Sgn_X ^ Sgn_Y );endproperty
assert property (SyncXorCheckeotid_2);

property SyncXorCheckeotid_3; @(posedge clk_in_19) ( Sgn_X ) != ( Sgn_Y ) &&  (  cfg_14 ) |-> ( Sgn_Info ) != ( Sgn_X ^ Sgn_Y );endproperty
assert property (SyncXorCheckeotid_3);

endmodule