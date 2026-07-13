module DEMUX_sva (
    input logic CLK,
    input logic in,
    input logic [1:0] sel,
    input logic [3:0] out
);
    // DEMUX is purely combinational with no reset; assertions are sampled on CLK.

    // For sel==2'b00, out == {in, 3'b000}.
    demux_map_sel00: assert property (
        @(posedge CLK) (sel == 2'b00) |-> (out == {in, 3'b000})
    );

    // For sel==2'b01, out == {3'b000, in}.
    demux_map_sel01: assert property (
        @(posedge CLK) (sel == 2'b01) |-> (out == {3'b000, in})
    );

    // For sel==2'b10, out == {2'b00, in, 1'b0}.
    demux_map_sel10: assert property (
        @(posedge CLK) (sel == 2'b10) |-> (out == {2'b00, in, 1'b0})
    );

    // For sel==2'b11, out == {1'b0, in, 2'b00}.
    demux_map_sel11: assert property (
        @(posedge CLK) (sel == 2'b11) |-> (out == {1'b0, in, 2'b00})
    );

    // Outputs are one-hot or all zero.
    demux_onehot_or_zero: assert property (
        @(posedge CLK) $onehot0(out)
    );

    // When in is 0, all outputs are 0.
    demux_zero_when_in0: assert property (
        @(posedge CLK) (in == 1'b0) |-> (out == 4'b0000)
    );

    // When in is 1, at least one output is 1.
    demux_nonzero_when_in1: assert property (
        @(posedge CLK) (in == 1'b1) |-> (out != 4'b0000)
    );

    // OR-reduce of out equals in.
    demux_or_reduce_matches_in: assert property (
        @(posedge CLK) ((|out) == in)
    );

    // out[3] can be 1 only when sel==2'b00 and in==1.
    demux_out3_only_when_sel00_in1: assert property (
        @(posedge CLK) (out[3] == 1'b1) |-> ((sel == 2'b00) && (in == 1'b1))
    );

    // out[2] can be 1 only when sel==2'b11 and in==1.
    demux_out2_only_when_sel11_in1: assert property (
        @(posedge CLK) (out[2] == 1'b1) |-> ((sel == 2'b11) && (in == 1'b1))
    );

    // out[1] can be 1 only when sel==2'b10 and in==1.
    demux_out1_only_when_sel10_in1: assert property (
        @(posedge CLK) (out[1] == 1'b1) |-> ((sel == 2'b10) && (in == 1'b1))
    );

    // out[0] can be 1 only when sel==2'b01 and in==1.
    demux_out0_only_when_sel01_in1: assert property (
        @(posedge CLK) (out[0] == 1'b1) |-> ((sel == 2'b01) && (in == 1'b1))
    );

endmodule