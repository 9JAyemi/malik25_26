module TLU_sva (
    input logic CK,
    input logic EN,
    input logic Q,
    input logic SE
);

property EnableSynceotid; @(posedge CK) (EN) |-> Q == SE ;endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge CK) (EN) |-> Q == SE ;endproperty
assert property (EnableSynceotid_2);

endmodule