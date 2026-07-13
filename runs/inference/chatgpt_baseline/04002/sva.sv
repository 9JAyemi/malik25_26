module decoder_sva (
    input logic        clk,
    input logic        A,
    input logic        B,
    input logic [15:0] O
);

    // Sample the combinational decoder on clk; the RTL has no reset.
    
    // A=0 and B=0 must drive only O[0] high.
    check_decode_00: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b0)) |-> (O === 16'h0001)
    );

    // A=0 and B=1 must drive only O[1] high.
    check_decode_01: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b1)) |-> (O === 16'h0002)
    );

    // A=1 and B=0 must drive only O[2] high.
    check_decode_10: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b0)) |-> (O === 16'h0004)
    );

    // A=1 and B=1 must drive only O[3] high.
    check_decode_11: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b1)) |-> (O === 16'h0008)
    );

    // Unknown or non-binary inputs must select the default all-zero output.
    check_default_zero_on_unknown: assert property (
        @(posedge clk)
        ((((A !== 1'b0) && (A !== 1'b1)) || ((B !== 1'b0) && (B !== 1'b1))))
        |-> (O === 16'h0000)
    );

    // The RTL never drives any output bit above O[3].
    check_upper_outputs_zero: assert property (
        @(posedge clk) (O[15:4] === 12'h000)
    );

    // The active decoded output in O[3:0] is one-hot or all-zero.
    check_low_nibble_onehot0: assert property (
        @(posedge clk) $onehot0(O[3:0])
    );

endmodule