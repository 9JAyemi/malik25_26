module decoder_4to16_sva (
    input logic [1:0] sel,
    input logic [15:0] out
);
    // Output equals 1'h1 shifted by sel (core decode relation).
    check_decode_equivalence: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        out == (16'b0000000000000001 << sel)
    );

    // Output is always one of the four valid patterns.
    check_out_valid_set: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        out inside {16'h0001,16'h0002,16'h0004,16'h0008}
    );

    // Upper bits [15:4] are always zero.
    check_upper_bits_zero: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        out[15:4] == 12'b0
    );

    // Exactly one output bit is HIGH at a time.
    check_onehot_out: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        $onehot(out)
    );

    // sel==2'b00 maps to out==16'h0001.
    check_map_00_forward: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b00) |=> (out == 16'h0001)
    );

    // sel==2'b01 maps to out==16'h0002.
    check_map_01_forward: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b01) |=> (out == 16'h0002)
    );

    // sel==2'b10 maps to out==16'h0004.
    check_map_10_forward: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b10) |=> (out == 16'h0004)
    );

    // sel==2'b11 maps to out==16'h0008.
    check_map_11_forward: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (sel == 2'b11) |=> (out == 16'h0008)
    );

    // Reverse: out==16'h0001 implies sel==2'b00.
    check_map_0001_reverse: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (out == 16'h0001) |=> (sel == 2'b00)
    );

    // Reverse: out==16'h0002 implies sel==2'b01.
    check_map_0002_reverse: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (out == 16'h0002) |=> (sel == 2'b01)
    );

    // Reverse: out==16'h0004 implies sel==2'b10.
    check_map_0004_reverse: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (out == 16'h0004) |=> (sel == 2'b10)
    );

    // Reverse: out==16'h0008 implies sel==2'b11.
    check_map_0008_reverse: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        (out == 16'h0008) |=> (sel == 2'b11)
    );

    // Out is never all zeros (default branch unreachable for 2-bit sel).
    check_out_nonzero: assert property (
        @(posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1])
        out != 16'h0000
    );
endmodule