module decoder_4to16_sva (
    input logic [255:0] in,
    input logic [3:0] sel,
    output logic [15:0] out
);
    // The logic is purely combinational as there is no sequential behavior.

    // The decoder should output a single bit set to 1 corresponding to the selected index.
    // All other bits should be 0.
    comb_decoder: assert property (
        @(posedge CLK) disable iff (!RESETn) 
        (sel inside {[0:15]} && out == (1 << sel)) || (sel outside {[0:15]} && out == 16'b0000000000000000)
    ) else $error("Decoder output is incorrect for sel = %h", sel);

    // The input in is not used in the decoder logic, so it should not affect the output.
    // This is a trivial assertion to ensure the input is not driving the output.
    input_unused: assert property (
        @(posedge CLK) disable iff (!RESETn) 
        (in == 256'b0) || (out == 16'b0000000000000000)
    ) else $error("Input in is driving the output, which should not happen.");

endmodule