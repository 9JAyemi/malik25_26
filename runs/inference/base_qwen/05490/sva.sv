module adder_4bit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    output logic [3:0] S,
    output logic Cout
);

    // Full adder logic is combinational, but we will use clocked assertions for consistency.

    // Cin can only transition from HIGH to LOW when all outputs are LOW.
    cin_transition: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(Cin) |-> (S == 4'b0000) && (Cout == 1'b0)
    );

    // Cin can only transition from LOW to HIGH when all inputs are LOW.
    cin_transition_2: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(Cin) |-> (A == 4'b0000) && (B == 4'b0000) && (S == 4'b0000)
    );

    // At reset assertion, all outputs must be LOW.
    reset: assert property (
        @(posedge CLK) !RESETn |-> (S == 4'b0000) && (Cout == 1'b0)
    );

endmodule