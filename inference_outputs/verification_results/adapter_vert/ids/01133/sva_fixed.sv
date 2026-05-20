module address_to_signal_sva (
    input logic address,
    input logic clock,
    input logic q,
    input logic b00
);

property ClockSynceotid; @(posedge clock) (address) |-> (q == {address, 2'b00}); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clock) (clock) |-> (q != address); endproperty
assert property (ClockSynceotid_2);

endmodule