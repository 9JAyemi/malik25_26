module memory_module_sva (
    input logic A1ADDR,
    input logic A1DATA,
    input logic A1EN,
    input logic B1ADDR,
    input logic B1DATA,
    input logic CLK1,
    input logic mem
);

property ClockSynceotid; @(posedge CLK1) (A1EN) |-> mem[A1ADDR] == A1DATA ;endproperty
assert property (ClockSynceotid);

property SyncLoadeotid; @(posedge CLK1) (B1ADDR) |-> B1DATA == mem[B1ADDR] ;endproperty
assert property (SyncLoadeotid);

endmodule