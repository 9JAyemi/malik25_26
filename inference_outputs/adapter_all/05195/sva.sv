module twos_complement_sva (
    input logic [3:0] a,
    input logic [3:0] twos_comp
);
    // twos_comp equals bitwise NOT of a plus 1 (4-bit 2's complement).
    check_twos_comp_def: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        twos_comp == (~a + 4'b0001)
    );

    // twos_comp + a equals zero modulo 16.
    check_additive_inverse: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        (twos_comp + a) == 4'b0000
    );

    // Zero input produces zero output.
    check_zero_maps_to_zero: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        (a == 4'b0000) |-> (twos_comp == 4'b0000)
    );

    // 4'b1000 maps to itself (only value that is its own 2's complement in 4 bits).
    check_min_negative_self_inverse: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        (a == 4'b1000) |-> (twos_comp == 4'b1000)
    );

    // twos_comp is never 4'b1111 (no 4-bit value is its own 2's complement).
    check_no_all_ones_output: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        twos_comp != 4'b1111
    );

    // twos_comp is never 4'b0001 (no 4-bit value is its own 2's complement).
    check_no_one_output: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        twos_comp != 4'b0001
    );

    // twos_comp is never 4'b1001 (no 4-bit value is its own 2's complement).
    check_no_nine_output: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        twos_comp != 4'b1001
    );

    // twos_comp is never 4'b1010 (no 4-bit value is its own 2's complement).
    check_no_ten_output: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        twos_comp != 4'b1010
    );

    // twos_comp is never 4'b1011 (no 4-bit value is its own 2's complement).
    check_no_eleven_output: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        twos_comp != 4'b1011
    );

    // twos_comp is never 4'b1100 (no 4-bit value is its own 2's complement).
    check_no_twelve_output: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        twos_comp != 4'b1100
    );

    // twos_comp is never 4'b1101 (no 4-bit value is its own 2's complement).
    check_no_thirteen_output: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        twos_comp != 4'b1101
    );

    // twos_comp is never 4'b1110 (no 4-bit value is its own 2's complement).
    check_no_fourteen_output: assert property (
        @(posedge a[0] or negedge a[0] or posedge a[1] or negedge a[1] or posedge a[2] or negedge a[2] or posedge a[3] or negedge a[3])
        twos_comp != 4'b1110
    );
endmodule