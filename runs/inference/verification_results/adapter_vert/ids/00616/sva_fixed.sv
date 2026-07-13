module FFType_sva (
    input logic clock,
    input logic d,
    input logic io_enable,
    input logic io_in,
    input logic io_init,
    input logic reset
);

property ResetSynceotid; @(posedge clock) (reset) |-> (d == io_init) ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clock) ( !reset ) &&  (  io_enable ) |-> (d == io_in) ;endproperty
assert property (EnableSynceotid);

endmodule