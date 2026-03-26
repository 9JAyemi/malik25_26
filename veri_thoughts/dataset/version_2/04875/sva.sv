module decoder_8to64_sva (
    input logic [7:0] ABCDEFGH,
    input logic [63:0] Y,
    input logic [5:0] stage
);

    // A zero stage advances to the first active stage.
    check_stage_zero_advances: assert property (
        @(posedge ABCDEFGH[7]) (stage == 6'b000000) |=> (stage == 6'b000001)
    );

    // Any nonzero stage shifts left by one bit.
    check_stage_nonzero_shifts_left: assert property (
        @(posedge ABCDEFGH[7]) (stage != 6'b000000) |=> (stage == {$past(stage[4:0]), 1'b0})
    );

    // Stage 0 drives 64'h40 onto Y on the following clock.
    check_output_for_stage_zero: assert property (
        @(posedge ABCDEFGH[7]) (stage == 6'b000000) |=> (Y == 64'h0000000000000040)
    );

    // Stage 1 drives 64'h01 onto Y on the following clock.
    check_output_for_stage_one: assert property (
        @(posedge ABCDEFGH[7]) (stage == 6'b000001) |=> (Y == 64'h0000000000000001)
    );

    // Stage 2 drives 64'h02 onto Y on the following clock.
    check_output_for_stage_two: assert property (
        @(posedge ABCDEFGH[7]) (stage == 6'b000010) |=> (Y == 64'h0000000000000002)
    );

    // Stage 4 drives 64'h04 onto Y on the following clock.
    check_output_for_stage_four: assert property (
        @(posedge ABCDEFGH[7]) (stage == 6'b000100) |=> (Y == 64'h0000000000000004)
    );

    // Stage 8 drives 64'h08 onto Y on the following clock.
    check_output_for_stage_eight: assert property (
        @(posedge ABCDEFGH[7]) (stage == 6'b001000) |=> (Y == 64'h0000000000000008)
    );

    // Stage 16 drives 64'h10 onto Y on the following clock.
    check_output_for_stage_sixteen: assert property (
        @(posedge ABCDEFGH[7]) (stage == 6'b010000) |=> (Y == 64'h0000000000000010)
    );

    // Stage 32 drives 64'h20 onto Y on the following clock.
    check_output_for_stage_thirty_two: assert property (
        @(posedge ABCDEFGH[7]) (stage == 6'b100000) |=> (Y == 64'h0000000000000020)
    );

    // Any unmapped stage drives zero onto Y on the following clock.
    check_output_zero_for_invalid_stage: assert property (
        @(posedge ABCDEFGH[7])
        (stage != 6'b000000 &&
         stage != 6'b000001 &&
         stage != 6'b000010 &&
         stage != 6'b000100 &&
         stage != 6'b001000 &&
         stage != 6'b010000 &&
         stage != 6'b100000)
        |=> (Y == 64'h0000000000000000)
    );

endmodule

bind decoder_8to64 decoder_8to64_sva u_decoder_8to64_sva (
    .ABCDEFGH(ABCDEFGH),
    .Y(Y),
    .stage(stage)
);