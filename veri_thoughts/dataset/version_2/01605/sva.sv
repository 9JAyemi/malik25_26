module top_module_sva (
    // External clock for sampling assertions (RTL has no clock/reset)
    input logic clk,
    // DUT ports
    input wire [15:0] in,
    input wire [10:0] out
);
    // Analysis:
    // - No clock/reset in RTL; logic is purely combinational.
    // - out[2:0] = priority_encoder(~in[15:8]); default 3'b111.
    // - out[10:3] = ((~in[15:8]) + (~in[7:0]))[7:0] (8-bit truncated sum).

    ///// Encoder correctness /////
    // out[2:0] matches the case mapping implemented in priority_encoder.
    check_encoder_functional_map: assert property (
        @(posedge clk) disable iff (1'b0)
            out[2:0] == (
                ((~in[15:8]) == 8'b00000001) ? 3'd0 :
                ((~in[15:8]) == 8'b00000010) ? 3'd1 :
                ((~in[15:8]) == 8'b00000100) ? 3'd2 :
                ((~in[15:8]) == 8'b00001000) ? 3'd3 :
                ((~in[15:8]) == 8'b00010000) ? 3'd4 :
                ((~in[15:8]) == 8'b00100000) ? 3'd5 :
                ((~in[15:8]) == 8'b01000000) ? 3'd6 :
                3'd7 // 8'b10000000 or any other pattern -> 3'b111
            )
    );

    // If only bit 0 of ~in[15:8] is set, encoder outputs 0.
    check_encoder_onehot_b0: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[15:8]) == 8'b00000001) |-> (out[2:0] == 3'd0)
    );

    // If only bit 1 of ~in[15:8] is set, encoder outputs 1.
    check_encoder_onehot_b1: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[15:8]) == 8'b00000010) |-> (out[2:0] == 3'd1)
    );

    // If only bit 2 of ~in[15:8] is set, encoder outputs 2.
    check_encoder_onehot_b2: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[15:8]) == 8'b00000100) |-> (out[2:0] == 3'd2)
    );

    // If only bit 3 of ~in[15:8] is set, encoder outputs 3.
    check_encoder_onehot_b3: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[15:8]) == 8'b00001000) |-> (out[2:0] == 3'd3)
    );

    // If only bit 4 of ~in[15:8] is set, encoder outputs 4.
    check_encoder_onehot_b4: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[15:8]) == 8'b00010000) |-> (out[2:0] == 3'd4)
    );

    // If only bit 5 of ~in[15:8] is set, encoder outputs 5.
    check_encoder_onehot_b5: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[15:8]) == 8'b00100000) |-> (out[2:0] == 3'd5)
    );

    // If only bit 6 of ~in[15:8] is set, encoder outputs 6.
    check_encoder_onehot_b6: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[15:8]) == 8'b01000000) |-> (out[2:0] == 3'd6)
    );

    // If no bits are set in ~in[15:8], encoder outputs 3'b111.
    check_encoder_default_zero: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[15:8]) == 8'b00000000) |-> (out[2:0] == 3'd7)
    );

    // If multiple bits are set in ~in[15:8], encoder outputs 3'b111.
    check_encoder_default_multibit: assert property (
        @(posedge clk) disable iff (1'b0)
            (((~in[15:8]) != 8'h00) && (((~in[15:8]) & ((~in[15:8]) - 8'h01)) != 8'h00))) |-> (out[2:0] == 3'd7)
    );

    ///// Sum path correctness /////
    // out[10:3] is the low 8 bits of (~in[15:8] + ~in[7:0]).
    check_sum_truncated: assert property (
        @(posedge clk) disable iff (1'b0)
            out[10:3] == ((~in[15:8]) + (~in[7:0]))[7:0]
    );

    // If ~in[7:0] is zero, sum equals ~in[15:8].
    check_sum_when_lower_zero: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[7:0]) == 8'h00) |-> (out[10:3] == (~in[15:8]))
    );

    // If ~in[15:8] is zero, sum equals ~in[7:0].
    check_sum_when_upper_zero: assert property (
        @(posedge clk) disable iff (1'b0)
            ((~in[15:8]) == 8'h00) |-> (out[10:3] == (~in[7:0]))
    );

    // If in == 16'hFFFF, both inverted bytes are zero and the sum is zero.
    check_sum_min: assert property (
        @(posedge clk) disable iff (1'b0)
            (in == 16'hFFFF) |-> (out[10:3] == 8'h00)
    );

    // If in == 16'h0000, both inverted bytes are 8'hFF and sum[7:0] == 8'hFE.
    check_sum_max_trunc: assert property (
        @(posedge clk) disable iff (1'b0)
            (in == 16'h0000) |-> (out[10:3] == 8'hFE)
    );

endmodule