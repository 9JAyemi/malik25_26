module four_bit_adder_sva (
    input logic A,
    input logic B,
    input logic Cin,
    input logic Clock,
    input logic Sum
);

property AdderSynceotid; @(posedge Clock) (A) + (B) + (Cin) == (Sum) ;endproperty
assert property (AdderSynceotid);

property SyncAddereotid; @(posedge Clock) (A) + (B) + (Cin) == (Sum) ;endproperty
assert property (SyncAddereotid);

property SyncAddereotid_2; @(posedge Clock) (A) + (B) + (Cin) == (Sum) ;endproperty
assert property (SyncAddereotid_2);

property SyncAddereotid_3; @(posedge Clock) (A) + (B) + (Cin) == (Sum) ;endproperty
assert property (SyncAddereotid_3);

endmodule