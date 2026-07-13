module memory_module_sva (
    input logic [4:0] A1ADDR,
    input logic A1DATA,
    input logic A1EN,
    input logic CLK1,
    input logic [4:0] B1ADDR,
    input logic B1DATA
);

    // B1DATA is the selected bit of the registered memory.
    check_b1data_matches_memory: assert property (
        @(posedge CLK1) 1'b1 |-> (B1DATA == $past(mem[B1ADDR]))
    );

    // A1EN high at the previous clock loads A1DATA into the memory bit at A1ADDR.
    check_memory_load_when_enabled: assert property (
        @(posedge CLK1) $past(A1EN) |-> (mem[$past(A1ADDR)] == $past(A1DATA))
    );

    // A1EN low at the previous clock leaves the memory bit at A1ADDR unchanged.
    check_memory_hold_when_disabled: assert property (
        @(posedge CLK1) !$past(A1EN) |-> (mem[$past(A1ADDR)] == $past(mem[$past(A1ADDR)]))
    );

    // A1ADDR and A1DATA do not affect the memory when A1EN is low.
    check_memory_ignored_when_disabled: assert property (
        @(posedge CLK1) (!$past(A1EN) && ($past(A1ADDR) == A1ADDR) && ($past(A1DATA) == A1DATA)) |-> (mem[$past(A1ADDR)] == $past(mem[$past(A1ADDR)]))
    );

endmodule