module decoder_3to8_case_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic [7:0] Y
);
    ///// Functional decoding checks /////
    // Y must equal 1 << {A,B,C} for any change on A/B/C.
    check_decode_shift_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        Y == (8'b00000001 << {A,B,C})
    );

    // Output must be one-hot for any change on A/B/C.
    check_onehot_output: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        $onehot(Y)
    );

    // When ABC=000, Y must be 00000001.
    check_decode_000: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        ({A,B,C} == 3'b000) |-> (Y == 8'b00000001)
    );

    // When ABC=001, Y must be 00000010.
    check_decode_001: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        ({A,B,C} == 3'b001) |-> (Y == 8'b00000010)
    );

    // When ABC=010, Y must be 00000100.
    check_decode_010: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        ({A,B,C} == 3'b010) |-> (Y == 8'b00000100)
    );

    // When ABC=011, Y must be 00001000.
    check_decode_011: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        ({A,B,C} == 3'b011) |-> (Y == 8'b00001000)
    );

    // When ABC=100, Y must be 00010000.
    check_decode_100: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        ({A,B,C} == 3'b100) |-> (Y == 8'b00010000)
    );

    // When ABC=101, Y must be 00100000.
    check_decode_101: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        ({A,B,C} == 3'b101) |-> (Y == 8'b00100000)
    );

    // When ABC=110, Y must be 01000000.
    check_decode_110: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        ({A,B,C} == 3'b110) |-> (Y == 8'b01000000)
    );

    // When ABC=111, Y must be 10000000.
    check_decode_111: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        disable iff (1'b0)
        ({A,B,C} == 3'b111) |-> (Y == 8'b10000000)
    );
endmodule