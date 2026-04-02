module sky130_fd_sc_hvl__a22o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    output logic X
);
    // The logic is purely combinational as there are no sequential elements.

    // A1 and A2 must both be 0 for X to be 0.
    comb_1: assert property (
        @(posedge clk) disable iff (!RESETn) (A1 == 1'b0) && (A2 == 1'b0) |-> (X == 1'b0)
    );

    // A1 or A2 must be 1 for X to be 1.
    comb_2: assert property (
        @(posedge clk) disable iff (!RESETn) (A1 == 1'b1) || (A2 == 1'b1) |-> (X == 1'b1)
    );

    // B1 and B2 must both be 1 for X to be 1.
    comb_3: assert property (
        @(posedge clk) disable iff (!RESETn) (B1 == 1'b1) && (B2 == 1'b1) |-> (X == 1'b1)
    );

    // If A1 or A2 is 1, B1 and B2 must both be 1 for X to be 1.
    comb_4: assert property (
        @(posedge clk) disable iff (!RESETn) ((A1 == 1'b1) || (A2 == 1'b1)) |-> (B1 == 1'b1) && (B2 == 1'b1)
    );

    // If B1 or B2 is 0, A1 and A2 must both be 0 for X to be 0.
    comb_5: assert property (
        @(posedge clk) disable iff (!RESETn) ((B1 == 1'b0) || (B2 == 1'b0)) |-> (A1 == 1'b0) && (A2 == 1'b0)
    );

    // If A1 and A2 are both 1, B1 and B2 must both be 1 for X to be 1.
    comb_6: assert property (
        @(posedge clk) disable iff (!RESETn) (A1 == 1'b1) && (A2 == 1'b1) |-> (B1 == 1'b1) && (B2 == 1'b1)
    );

    // If A1 and A2 are both 0, B1 and B2 must both be 0 for X to be 0.
    comb_7: assert property (
        @(posedge clk) disable iff (!RESETn) (A1 == 1'b0) && (A2 == 1'b0) |-> (B1 == 1'b0) && (B2 == 1'b0)
    );

    // If B1 and B2 are both 1, A1 and A2 must both be 1 for X to be 1.
    comb_8: assert property (
        @(posedge clk) disable iff (!RESETn) (B1 == 1'b1) && (B2 == 1'b1) |-> (A1 == 1'b1) && (A2 == 1'b1)
    );

    // If B1 and B2 are both 0, A1 and A2 must both be 0 for X to be 0.
    comb_9: assert property (
        @(posedge clk) disable iff (!RESETn) (B1 == 1'b0) && (B2 == 1'b0) |-> (A1 == 1'b0) && (A2 == 1'b0)
    );

    // If A1 or A2 is 1, B1 and B2 must both be 1 for X to be 1.
    comb_10: assert property (
        @(posedge clk) disable iff (!RESETn) ((A1 == 1'b1) || (A2 == 1'b1)) |-> (B1 == 1'b1) && (B2 == 1'b1)
    );
endmodule