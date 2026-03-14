module priority_encoder_sva (
    input logic clk,
    input logic [2:0] in,
    input logic [7:0] out
);
    // Combinational 3->8 decoder; no reset in RTL; assertions sample on clk.

    // Output equals one-hot shift of input index.
    check_shift_equivalence: assert property (
        @(posedge clk) out == (8'b00000001 << in)
    );

    // Output is exactly one-hot.
    check_onehot_out: assert property (
        @(posedge clk) $onehot(out)
    );

    // When in==000, out==00000001.
    check_decode_000: assert property (
        @(posedge clk) (in == 3'b000) |-> (out == 8'b00000001)
    );

    // When in==001, out==00000010.
    check_decode_001: assert property (
        @(posedge clk) (in == 3'b001) |-> (out == 8'b00000010)
    );

    // When in==010, out==00000100.
    check_decode_010: assert property (
        @(posedge clk) (in == 3'b010) |-> (out == 8'b00000100)
    );

    // When in==011, out==00001000.
    check_decode_011: assert property (
        @(posedge clk) (in == 3'b011) |-> (out == 8'b00001000)
    );

    // When in==100, out==00010000.
    check_decode_100: assert property (
        @(posedge clk) (in == 3'b100) |-> (out == 8'b00010000)
    );

    // When in==101, out==00100000.
    check_decode_101: assert property (
        @(posedge clk) (in == 3'b101) |-> (out == 8'b00100000)
    );

    // When in==110, out==01000000.
    check_decode_110: assert property (
        @(posedge clk) (in == 3'b110) |-> (out == 8'b01000000)
    );

    // When in==111, out==10000000.
    check_decode_111: assert property (
        @(posedge clk) (in == 3'b111) |-> (out == 8'b10000000)
    );
endmodule