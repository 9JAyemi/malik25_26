module ripple_adder_sva (
    // External sampling clock for assertions (RTL has no clock/reset)
    input logic CLK,
    // DUT ports (ripple_adder)
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum,
    input logic       carry_out
);
    // RTL has no clock or reset; logic is purely combinational (8-bit ripple-carry adder with 1-bit carry_out).

    // Local 9-bit unsigned sum of a and b (models zero carry-in).
    logic [8:0] ext_sum;
    assign ext_sum = {1'b0, a} + {1'b0, b};

    // Sum and carry must equal the 9-bit unsigned addition of a and b.
    check_addition_9bit: assert property (
        @(posedge CLK) {carry_out, sum} == ext_sum
    );

    // Carry_out equals the MSB of the 9-bit extended sum.
    check_carry_bit: assert property (
        @(posedge CLK) carry_out == ext_sum[8]
    );

    // MSB of sum equals bit 7 of the 9-bit extended sum.
    check_sum_msb: assert property (
        @(posedge CLK) sum[7] == ext_sum[7]
    );

    // LSB of sum equals a[0] XOR b[0] (since c_in=0 at bit 0).
    check_sum_lsb_no_cin: assert property (
        @(posedge CLK) sum[0] == (a[0] ^ b[0])
    );

    // Adding zero on a passes b through with no carry.
    check_a_zero_passthrough: assert property (
        @(posedge CLK) (a == 8'h00) |-> (sum == b) && (carry_out == 1'b0)
    );

    // Adding zero on b passes a through with no carry.
    check_b_zero_passthrough: assert property (
        @(posedge CLK) (b == 8'h00) |-> (sum == a) && (carry_out == 1'b0)
    );

    // If both MSBs are 0, no overflow (carry_out) can occur.
    check_no_overflow_msbs_clear: assert property (
        @(posedge CLK) ((a[7] == 1'b0) && (b[7] == 1'b0)) |-> (carry_out == 1'b0)
    );

    // If both MSBs are 1, overflow (carry_out) must occur.
    check_overflow_msbs_set: assert property (
        @(posedge CLK) ((a[7] == 1'b1) && (b[7] == 1'b1)) |-> (carry_out == 1'b1)
    );

    // When a & b has no common 1s, sum equals a ^ b and carry_out is 0.
    check_xor_when_no_overlap: assert property (
        @(posedge CLK) ((a & b) == 8'h00) |-> ((sum == (a ^ b)) && (carry_out == 1'b0))
    );

    // 0xFF + 0x01 results in sum 0x00 with carry_out 1.
    check_ff_plus_one: assert property (
        @(posedge CLK) ((a == 8'hFF) && (b == 8'h01)) |-> ((sum == 8'h00) && (carry_out == 1'b1))
    );
endmodule