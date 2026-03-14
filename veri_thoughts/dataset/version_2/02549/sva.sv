module decoder_sva (
    input logic CLK,
    input logic [2:0] ABC,
    input logic [7:0] Y
);
    ///// Functional decode checks /////
    // Y must always be exactly one-hot.
    check_y_onehot: assert property (
        @(posedge CLK) $onehot(Y)
    );

    // Y must equal 1 shifted left by ABC.
    check_decode_shift: assert property (
        @(posedge CLK) Y == (8'b00000001 << ABC)
    );

    ///// Inverse mapping: Y bit implies ABC value /////
    // If Y[0] is HIGH, ABC must be 000.
    check_y0_implies_abc0: assert property (
        @(posedge CLK) Y[0] |-> (ABC == 3'b000)
    );

    // If Y[1] is HIGH, ABC must be 001.
    check_y1_implies_abc1: assert property (
        @(posedge CLK) Y[1] |-> (ABC == 3'b001)
    );

    // If Y[2] is HIGH, ABC must be 010.
    check_y2_implies_abc2: assert property (
        @(posedge CLK) Y[2] |-> (ABC == 3'b010)
    );

    // If Y[3] is HIGH, ABC must be 011.
    check_y3_implies_abc3: assert property (
        @(posedge CLK) Y[3] |-> (ABC == 3'b011)
    );

    // If Y[4] is HIGH, ABC must be 100.
    check_y4_implies_abc4: assert property (
        @(posedge CLK) Y[4] |-> (ABC == 3'b100)
    );

    // If Y[5] is HIGH, ABC must be 101.
    check_y5_implies_abc5: assert property (
        @(posedge CLK) Y[5] |-> (ABC == 3'b101)
    );

    // If Y[6] is HIGH, ABC must be 110.
    check_y6_implies_abc6: assert property (
        @(posedge CLK) Y[6] |-> (ABC == 3'b110)
    );

    // If Y[7] is HIGH, ABC must be 111.
    check_y7_implies_abc7: assert property (
        @(posedge CLK) Y[7] |-> (ABC == 3'b111)
    );
endmodule