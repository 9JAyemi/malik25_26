module sum16bits_sva (
    input logic clk,              // verification clock (DUT is combinational)
    input logic [15:0] input16,
    input logic [7:0]  output8
);
    // Output equals low 8 bits of upper+lower bytes.
    check_modulo_add: assert property (
        @(posedge clk) output8 == ({1'b0, input16[15:8]} + {1'b0, input16[7:0]})[7:0]
    );

    // If upper byte is zero, output equals lower byte.
    check_upper_zero_passthrough: assert property (
        @(posedge clk) (input16[15:8] == 8'h00) |-> (output8 == input16[7:0])
    );

    // If lower byte is zero, output equals upper byte.
    check_lower_zero_passthrough: assert property (
        @(posedge clk) (input16[7:0] == 8'h00) |-> (output8 == input16[15:8])
    );

    // Complementary bytes (lower = ~upper) sum to 0xFF.
    check_complementary_bytes_ff: assert property (
        @(posedge clk) (input16[7:0] == ~input16[15:8]) |-> (output8 == 8'hFF)
    );

    // Exact sum of 256 wraps output to 0.
    check_exact_256_sum_wraps_zero: assert property (
        @(posedge clk) (({1'b0, input16[15:8]} + {1'b0, input16[7:0]}) == 9'h100) |-> (output8 == 8'h00)
    );

    // Upper byte 0xFF causes output to be lower-1 (mod 256).
    check_upper_ff_decrements_lower: assert property (
        @(posedge clk) (input16[15:8] == 8'hFF) |-> (output8 == (input16[7:0] - 8'h01))
    );

    // Lower byte 0xFF causes output to be upper-1 (mod 256).
    check_lower_ff_decrements_upper: assert property (
        @(posedge clk) (input16[7:0] == 8'hFF) |-> (output8 == (input16[15:8] - 8'h01))
    );

    // Upper byte 0x01 increments lower (mod 256).
    check_upper_one_increments_lower: assert property (
        @(posedge clk) (input16[15:8] == 8'h01) |-> (output8 == (input16[7:0] + 8'h01))
    );

    // Lower byte 0x01 increments upper (mod 256).
    check_lower_one_increments_upper: assert property (
        @(posedge clk) (input16[7:0] == 8'h01) |-> (output8 == (input16[15:8] + 8'h01))
    );

    // Equal bytes double (shift left by 1) modulo 256.
    check_equal_halves_double_mod256: assert property (
        @(posedge clk) (input16[15:8] == input16[7:0]) |-> (output8 == (input16[7:0] << 1))
    );
endmodule