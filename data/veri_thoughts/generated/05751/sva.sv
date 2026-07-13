module altpriority_encoder_6_3_lh_sva (
    input logic clk,
    input logic [5:0] data,
    input logic [2:0] q
);

    // 000001 maps to 000.
    check_encode_000001: assert property (
        @(posedge clk) (data == 6'b000001) |-> (q == 3'b000)
    );

    // 000010 maps to 001.
    check_encode_000010: assert property (
        @(posedge clk) (data == 6'b000010) |-> (q == 3'b001)
    );

    // 000100 maps to 010.
    check_encode_000100: assert property (
        @(posedge clk) (data == 6'b000100) |-> (q == 3'b010)
    );

    // 001000 maps to 011.
    check_encode_001000: assert property (
        @(posedge clk) (data == 6'b001000) |-> (q == 3'b011)
    );

    // 010000 maps to 100.
    check_encode_010000: assert property (
        @(posedge clk) (data == 6'b010000) |-> (q == 3'b100)
    );

    // 100000 maps to 101.
    check_encode_100000: assert property (
        @(posedge clk) (data == 6'b100000) |-> (q == 3'b101)
    );

    // All other inputs map to the default code.
    check_default_encoding: assert property (
        @(posedge clk)
        (data != 6'b000001 &&
         data != 6'b000010 &&
         data != 6'b000100 &&
         data != 6'b001000 &&
         data != 6'b010000 &&
         data != 6'b100000) |-> (q == 3'b110)
    );

    // The output never produces 111.
    check_q_never_111: assert property (
        @(posedge clk) (q != 3'b111)
    );

endmodule