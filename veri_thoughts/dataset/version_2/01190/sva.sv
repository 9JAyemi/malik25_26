module and_or_gate_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F1,
    input logic F2,
    input logic and1,
    input logic and2,
    input logic or1
);
    // and1 must equal A & B.
    check_and1_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) and1 == (A & B)
    );

    // and2 must equal C & D.
    check_and2_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) and2 == (C & D)
    );

    // or1 must equal A | B.
    check_or1_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) or1 == (A | B)
    );

    // F1 must equal and1 & and2.
    check_F1_from_internals: assert property (
        @(posedge CLK) disable iff (!RESETn) F1 == (and1 & and2)
    );

    // F2 must equal or1 | and2.
    check_F2_from_internals: assert property (
        @(posedge CLK) disable iff (!RESETn) F2 == (or1 | and2)
    );

    // F1 must equal A & B & C & D.
    check_F1_from_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) F1 == (A & B & C & D)
    );

    // F2 must equal (A | B) | (C & D).
    check_F2_from_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) F2 == ((A | B) | (C & D))
    );

    // If F1 is HIGH then and1 must be HIGH.
    check_F1_implies_and1: assert property (
        @(posedge CLK) disable iff (!RESETn) F1 |-> (and1 == 1'b1)
    );

    // If F1 is HIGH then and2 must be HIGH.
    check_F1_implies_and2: assert property (
        @(posedge CLK) disable iff (!RESETn) F1 |-> (and2 == 1'b1)
    );

    // If and2 is HIGH then F2 must be HIGH.
    check_and2_implies_F2: assert property (
        @(posedge CLK) disable iff (!RESETn) and2 |-> (F2 == 1'b1)
    );
endmodule