module sky130_fd_sc_ls__o2111a_sva (
    input logic CLK,
    input logic RESETn,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    output logic X
);
    // Combinational logic: X is driven by the output of the AND gate
    // The AND gate's output is driven by the OR gate's output and the inputs B1, C1, A2, and D1
    // The OR gate's output is driven by the inputs A2 and A1
    // At reset, X should be LOW
    // The AND gate's output should be LOW when B1 or C1 is LOW
    // The OR gate's output should be LOW when A1 and A2 are both LOW

    // At reset, X should be LOW
    reset: assert property (
        @(posedge CLK) !RESETn |-> (X == 1'b0)
    );

    // The AND gate's output should be LOW when B1 or C1 is LOW
    and_output_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (B1 == 1'b0 || C1 == 1'b0) |-> (X == 1'b0)
    );

    // The OR gate's output should be LOW when A1 and A2 are both LOW
    or_output_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 == 1'b0 && A2 == 1'b0) |-> (X == 1'b0)
    );

    // The AND gate's output should be HIGH when B1 and C1 are both HIGH and A2 and D1 are both HIGH
    and_output_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (B1 == 1'b1 && C1 == 1'b1 && A2 == 1'b1 && D1 == 1'b1) |-> (X == 1'b1)
    );

    // The OR gate's output should be HIGH when A1 or A2 is HIGH
    or_output_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 == 1'b1 || A2 == 1'b1) |-> (X == 1'b1)
    );

endmodule