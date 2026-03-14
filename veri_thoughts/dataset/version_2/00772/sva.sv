module decoder_4to16_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [15:0] out
);
    ///// Decoder correctness /////
    // Out equals 1 shifted by 'in' (core 4->16 one-hot decode).
    check_decode_function: assert property (
        @(posedge clk) out == (16'h0001 << in)
    );

    // Out is exactly one-hot (exactly one bit set).
    check_out_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

    // If input is stable between cycles, output must be stable.
    check_out_stable_when_in_stable: assert property (
        @(posedge clk) $stable(in) |-> $stable(out)
    );

    // Any change on output must be due to a change on input.
    check_out_change_implies_in_change: assert property (
        @(posedge clk) $changed(out) |-> $changed(in)
    );

    ///// Specific mappings (spot-checks) /////
    // in == 0 maps to out == 16'h0001.
    check_map_in0: assert property (
        @(posedge clk) (in == 4'd0) |-> (out == 16'h0001)
    );

    // in == 1 maps to out == 16'h0002.
    check_map_in1: assert property (
        @(posedge clk) (in == 4'd1) |-> (out == 16'h0002)
    );

    // in == 14 maps to out == 16'h4000.
    check_map_in14: assert property (
        @(posedge clk) (in == 4'd14) |-> (out == 16'h4000)
    );

    // in == 15 maps to out == 16'h8000.
    check_map_in15: assert property (
        @(posedge clk) (in == 4'd15) |-> (out == 16'h8000)
    );
endmodule