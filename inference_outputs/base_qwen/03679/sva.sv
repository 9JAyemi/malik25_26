module fourBitAdder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    output logic [3:0] Sum,
    output logic Cout
);
    // Combinational logic: Sum and Cout are determined by A, B, and Cin
    // at the current clock edge.
    combinational_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (Sum == A + B + Cin) && (Cout == (A + B + Cin)[4])
    );
endmodule