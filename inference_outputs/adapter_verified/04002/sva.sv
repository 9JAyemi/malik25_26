module decoder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic [15:0] O
);

// When A=0 and B=0, O must be 0000_0000_0000_0001.
    check_decode_00: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0) |-> (O == 16'h0001)
    );

// When A=0 and B=1, O must be 0000_0000_0000_0010.
    check_decode_01: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b1) |-> (O == 16'h0002)
    );

// When A=1 and B=0, O must be 0000_0000_0000_0100.
    check_decode_10: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b0) |-> (O == 16'h0004)
    );

// When A=1 and B=1, O must be 0000_0000_0000_1000.
    check_decode_11: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1) |-> (O == 16'h0008)
    );

// When A=0 and B=0, only O0 can be high.
    check_onehot_00: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0) |-> (O == 16'h0001)
    );

// When A=0 and B=1, only O1 can be high.
    check_onehot_01: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b1) |-> (O == 16'h0002)
    );

// When A=1 and B=0, only O2 can be high.
    check_onehot_10: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b0) |-> (O == 16'h0004)
    );

// When A=1 and B=1, only O3 can be high.
    check_onehot_11: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1) |-> (O == 16'h0008)
    );

// O must always be one of the four allowed patterns.
    check_valid_output_pattern: assert property (
        @(posedge clk) (O == 16'h0001) || (O == 16'h0002) || (O == 16'h0004) || (O == 16'h0008)
    );

endmodule
