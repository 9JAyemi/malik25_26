module binary_converter_sva(
    input logic clk,
    input logic [3:0] DATA_IN,
    input logic [7:0] DATA_OUT
);

    // 0 encodes to bit 0 set.
    check_encode_0: assert property (
        @(posedge clk) (DATA_IN == 4'd0) |-> (DATA_OUT == 8'b00000001)
    );

    // 1 encodes to bit 1 set.
    check_encode_1: assert property (
        @(posedge clk) (DATA_IN == 4'd1) |-> (DATA_OUT == 8'b00000010)
    );

    // 2 encodes to bit 2 set.
    check_encode_2: assert property (
        @(posedge clk) (DATA_IN == 4'd2) |-> (DATA_OUT == 8'b00000100)
    );

    // 3 encodes to bit 3 set.
    check_encode_3: assert property (
        @(posedge clk) (DATA_IN == 4'd3) |-> (DATA_OUT == 8'b00001000)
    );

    // 4 encodes to bit 4 set.
    check_encode_4: assert property (
        @(posedge clk) (DATA_IN == 4'd4) |-> (DATA_OUT == 8'b00010000)
    );

    // 5 encodes to bit 5 set.
    check_encode_5: assert property (
        @(posedge clk) (DATA_IN == 4'd5) |-> (DATA_OUT == 8'b00100000)
    );

    // 6 encodes to bit 6 set.
    check_encode_6: assert property (
        @(posedge clk) (DATA_IN == 4'd6) |-> (DATA_OUT == 8'b01000000)
    );

    // 7 encodes to bit 7 set.
    check_encode_7: assert property (
        @(posedge clk) (DATA_IN == 4'd7) |-> (DATA_OUT == 8'b10000000)
    );

    // 8 encodes to bits 7 and 0 set.
    check_encode_8: assert property (
        @(posedge clk) (DATA_IN == 4'd8) |-> (DATA_OUT == 8'b10000001)
    );

    // 9 encodes to bits 7 and 1 set.
    check_encode_9: assert property (
        @(posedge clk) (DATA_IN == 4'd9) |-> (DATA_OUT == 8'b10000010)
    );

    // Inputs above 9 encode to zero.
    check_encode_default: assert property (
        @(posedge clk) (DATA_IN > 4'd9) |-> (DATA_OUT == 8'b00000000)
    );

endmodule