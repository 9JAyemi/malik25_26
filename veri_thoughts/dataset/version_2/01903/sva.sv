module four_bit_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);
    // Assertions sample on posedge of cin (no clock/reset in DUT).

    // Sum+cout must equal 5-bit arithmetic result of a + b + cin.
    check_add_full_concat_on_cin: assert property (
        @(posedge cin) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // sum[0] must be the XOR of a[0], b[0], and cin.
    check_sum0_xor: assert property (
        @(posedge cin) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // sum[1] must equal XOR of a[1], b[1], and carry from bit0.
    check_sum1_chain: assert property (
        @(posedge cin)
            sum[1] == (a[1] ^ b[1] ^
                      ((a[0] & b[0]) | ((a[0] ^ b[0]) & cin)))
    );

    // sum[2] must equal XOR of a[2], b[2], and carry from bit1.
    check_sum2_chain: assert property (
        @(posedge cin)
            sum[2] == (a[2] ^ b[2] ^
                      ((a[1] & b[1]) | ((a[1] ^ b[1]) &
                      ((a[0] & b[0]) | ((a[0] ^ b[0]) & cin)))))
    );

    // sum[3] must equal XOR of a[3], b[3], and carry from bit2.
    check_sum3_chain: assert property (
        @(posedge cin)
            sum[3] == (a[3] ^ b[3] ^
                      ((a[2] & b[2]) | ((a[2] ^ b[2]) &
                      ((a[1] & b[1]) | ((a[1] ^ b[1]) &
                      ((a[0] & b[0]) | ((a[0] ^ b[0]) & cin)))))))
    );

    // cout must equal carry from bit3.
    check_cout_chain: assert property (
        @(posedge cin)
            cout == ((a[3] & b[3]) | ((a[3] ^ b[3]) &
                   ((a[2] & b[2]) | ((a[2] ^ b[2]) &
                   ((a[1] & b[1]) | ((a[1] ^ b[1]) &
                   ((a[0] & b[0]) | ((a[0] ^ b[0]) & cin))))))))
    );

    // sum must match the lower 4 bits of a + b + cin.
    check_sum_lower_bits_from_arith: assert property (
        @(posedge cin) sum == ({1'b0, a} + {1'b0, b} + cin)[3:0]
    );

    // cout must match the MSB of a + b + cin.
    check_cout_from_arith: assert property (
        @(posedge cin) cout == ({1'b0, a} + {1'b0, b} + cin)[4]
    );

    // All zeros on inputs must yield zero sum and zero carry.
    check_zero_case: assert property (
        @(posedge cin) (a == 4'b0000 && b == 4'b0000 && cin == 1'b0) |-> (sum == 4'b0000 && cout == 1'b0)
    );

    // Max case 0xF + 0xF + 1 must yield sum=0xF and cout=1.
    check_max_case: assert property (
        @(posedge cin) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> (sum == 4'hF && cout == 1'b1)
    );
endmodule