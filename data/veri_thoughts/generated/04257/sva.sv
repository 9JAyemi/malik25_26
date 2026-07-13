module concat_split_vectors_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [3:0] w,
    input logic [3:0] x,
    input logic [3:0] y,
    input logic [3:0] z
);

    // The full output vector is the concatenated inputs plus 3.
    check_full_vector_sum: assert property (
        @($global_clock) {w, x, y, z} == ({a, b} + 16'h0003)
    );

    // The low output byte is b plus 3.
    check_low_byte_sum: assert property (
        @($global_clock) {y, z} == (b + 8'h03)
    );

    // The high output byte is unchanged when b plus 3 does not overflow.
    check_high_byte_no_carry: assert property (
        @($global_clock) (b < 8'hFD) |-> ({w, x} == a)
    );

    // The high output byte increments when b plus 3 overflows.
    check_high_byte_with_carry: assert property (
        @($global_clock) (b >= 8'hFD) |-> ({w, x} == (a + 8'h01))
    );

    // The lowest nibble is the low nibble of b plus 3.
    check_z_nibble_sum: assert property (
        @($global_clock) z == (b[3:0] + 4'h3)
    );

    // The next nibble includes carry from the low nibble addition.
    check_y_nibble_sum: assert property (
        @($global_clock) y == (b[7:4] + ((b[3:0] >= 4'hD) ? 4'h1 : 4'h0))
    );

    // The x nibble matches a[3:0] when there is no carry from b.
    check_x_nibble_no_carry: assert property (
        @($global_clock) (b < 8'hFD) |-> (x == a[3:0])
    );

    // The x nibble increments a[3:0] when b generates a byte carry.
    check_x_nibble_with_carry: assert property (
        @($global_clock) (b >= 8'hFD) |-> (x == (a[3:0] + 4'h1))
    );

    // The w nibble stays equal to a[7:4] unless carry propagates through x.
    check_w_nibble_no_upper_carry: assert property (
        @($global_clock) ((b < 8'hFD) || (a[3:0] != 4'hF)) |-> (w == a[7:4])
    );

    // The w nibble increments when carry from b propagates through a[3:0].
    check_w_nibble_with_upper_carry: assert property (
        @($global_clock) ((b >= 8'hFD) && (a[3:0] == 4'hF)) |-> (w == (a[7:4] + 4'h1))
    );

endmodule