module dff_en_sva (
    input logic C,
    input logic D,
    input logic E,
    input logic Q
);

property ClockSynceotid; @(posedge C) (E) |-> Q == D ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge C) (E) |-> Q == D ;endproperty
assert property (ClockSynceotid_2);

endmodule