module dec_5to32_assertions (
    input logic clk,
    input logic [4:0] a,
    input logic [31:0] b
);

    // Combinational decoder sampled on external clk; no reset in RTL.

    // Output must equal the one-hot decode of the 5-bit input.
    check_decode_matches_shift: assert property (
        @(posedge clk) b == (32'h0000_0001 << a)
    );

    // Exactly one output bit must be asserted.
    check_output_is_onehot: assert property (
        @(posedge clk) $onehot(b)
    );

    // Inputs with a[4:3]==00 can only drive outputs 0 through 7.
    check_quadrant_00_range: assert property (
        @(posedge clk) (a[4:3] == 2'b00) |-> (b[31:8] == 24'h0)
    );

    // Inputs with a[4:3]==01 can only drive outputs 8 through 15.
    check_quadrant_01_range: assert property (
        @(posedge clk) (a[4:3] == 2'b01) |-> ((b[31:16] == 16'h0) && (b[7:0] == 8'h0))
    );

    // Inputs with a[4:3]==10 can only drive outputs 16 through 23.
    check_quadrant_10_range: assert property (
        @(posedge clk) (a[4:3] == 2'b10) |-> ((b[31:24] == 8'h0) && (b[15:0] == 16'h0))
    );

    // Inputs with a[4:3]==11 can only drive outputs 24 through 31.
    check_quadrant_11_range: assert property (
        @(posedge clk) (a[4:3] == 2'b11) |-> (b[23:0] == 24'h0)
    );

    // Input 0 must select b[0].
    check_zero_input_decode: assert property (
        @(posedge clk) (a == 5'd0) |-> (b == 32'h0000_0001)
    );

    // Input 15 must select b[15].
    check_input_15_decode: assert property (
        @(posedge clk) (a == 5'd15) |-> (b == 32'h0000_8000)
    );

    // Input 16 must select b[16].
    check_input_16_decode: assert property (
        @(posedge clk) (a == 5'd16) |-> (b == 32'h0001_0000)
    );

    // Input 31 must select b[31].
    check_max_input_decode: assert property (
        @(posedge clk) (a == 5'd31) |-> (b == 32'h8000_0000)
    );

endmodule