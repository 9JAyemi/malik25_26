module mux_2_1_sva (
    input logic A,
    input logic B,
    input logic SEL,
    output logic Y
);
    // SEL can only transition from 0 to 1 when Y is equal to B.
    mux_2_1_property_1: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(SEL) |-> (Y == B)
    );
    // SEL can only transition from 1 to 0 when Y is equal to A.
    mux_2_1_property_2: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(SEL) |-> (Y == A)
    );
endmodule