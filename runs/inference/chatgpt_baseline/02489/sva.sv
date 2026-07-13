module ripple_adder_32_sva (
    input  logic        clk,
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic        cin,
    input  logic [31:0] sum,
    input  logic        cout
);
    ///// Arithmetic correctness /////
    // Sum+carry equals a+b+cin (33-bit unsigned addition).
    check_full_sum_concat: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Sum equals lower 32 bits of (a+b+cin).
    check_sum_lower_bits: assert property (
        @(posedge clk) sum == (({1'b0, a} + {1'b0, b} + cin)[31:0])
    );

    // Cout equals MSB (bit 32) of (a+b+cin).
    check_cout_bit: assert property (
        @(posedge clk) cout == (({1'b0, a} + {1'b0, b} + cin)[32])
    );

    ///// Bitwise relations /////
    // LSB sum equals a[0] ^ b[0] ^ cin.
    check_sum_bit0_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Each sum[i] equals a[i] ^ b[i] ^ carry_in_from_lower_bits.
    genvar i;
    generate
        for (i = 1; i < 32; i++) begin : gen_sum_bit_xor
            // sum[i] matches XOR with computed carry-in from bits [i-1:0].
            check_sum_bit_i_xor: assert property (
                @(posedge clk) sum[i] == (a[i] ^ b[i] ^ (({1'b0, a[i-1:0]} + {1'b0, b[i-1:0]} + cin)[i]))
            );
        end
    endgenerate

    ///// Simple identities /////
    // If b==0 and cin==0 then sum==a and cout==0.
    passthrough_b0_cin0: assert property (
        @(posedge clk) (b == 32'b0) && (cin == 1'b0) |-> (sum == a) && (cout == 1'b0)
    );

    // If a==0 and cin==0 then sum==b and cout==0.
    passthrough_a0_cin0: assert property (
        @(posedge clk) (a == 32'b0) && (cin == 1'b0) |-> (sum == b) && (cout == 1'b0)
    );

    // If a==0 and b==0 then sum==cin and cout==0.
    zero_plus_zero: assert property (
        @(posedge clk) (a == 32'b0) && (b == 32'b0) |-> (sum == {31'b0, cin}) && (cout == 1'b0)
    );

    // If a==~b and cin==1 then sum==0 and cout==1.
    ones_complement_plus1: assert property (
        @(posedge clk) (a == ~b) && (cin == 1'b1) |-> (sum == 32'b0) && (cout == 1'b1)
    );

    // If a==~b and cin==0 then sum==all_ones and cout==0.
    ones_complement_no_cin: assert property (
        @(posedge clk) (a == ~b) && (cin == 1'b0) |-> (sum == 32'hFFFF_FFFF) && (cout == 1'b0)
    );

    ///// Carry-out characterizations /////
    // With cin==0, cout equals unsigned carry from a+b.
    cout_when_cin0: assert property (
        @(posedge clk) (cin == 1'b0) |-> (cout == ((a + b) < a))
    );

    // With cin==1, cout equals carry_from(a+b) OR (a+b == all_ones).
    cout_when_cin1: assert property (
        @(posedge clk) (cin == 1'b1) |-> (cout == (((a + b) < a) || ((a + b) == 32'hFFFF_FFFF)))
    );
endmodule