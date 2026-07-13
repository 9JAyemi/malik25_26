module MUX4_1_SL_assertions (
    input logic CLK,
    input logic [1:0] Sel,
    input logic [3:0] S0,
    input logic [3:0] S1,
    input logic [3:0] S2,
    input logic [3:0] S3,
    output logic [3:0] out
);
    // Sequential logic is not present, so all assertions will be clocked.

    // MUX output should be one of the inputs based on the selection.
    mux_output: assert property (
        @(posedge CLK) disable iff (!CLK) (out == (Sel[1] ? (Sel[0] ? S3 : S2) : (Sel[0] ? S1 : S0)))
    );
endmodule