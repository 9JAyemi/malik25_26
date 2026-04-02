module mux2to1_sva (
    input logic A,
    input logic B,
    input logic SEL,
    output logic Y
);
    // Mux output Y should be equal to A when SEL is 0
    mux_output_A: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 0) |-> (Y == A)
    );
    // Mux output Y should be equal to B when SEL is 1
    mux_output_B: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 1) |-> (Y == B)
    );
endmodule