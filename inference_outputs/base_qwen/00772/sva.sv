module decoder_4to16_sva (
    input logic [3:0] in,
    output logic [15:0] out
);
    // Sequential logic assertion to check the decoder behavior
    decoder_behavior: assert property (
        @(posedge CLK) disable iff (!RESETn) (in inside {[0:15]}) |-> (out == {16{in}})
    ) else $error("Decoder output does not match expected value for input %h", in);
endmodule