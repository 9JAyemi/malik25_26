module binary_full_adder_74283_sva (
    input logic clk,
    input logic [3:0] num1,
    input logic [3:0] num2,
    input logic carry_in,
    input logic [3:0] sum,
    input logic carry_out
);
    function automatic logic maj3 (input logic a, input logic b, input logic c);
        maj3 = (a & b) | (a & c) | (b & c);
    endfunction

    // Sum and carry concatenation equals 5-bit addition of operands.
    check_full_sum_concat: assert property (
        @(posedge clk) {carry_out, sum} == (num1 + num2 + carry_in)
    );

    // LSB sum bit is XOR of inputs and carry_in.
    check_sum_bit0_xor: assert property (
        @(posedge clk) sum[0] == (num1[0] ^ num2[0] ^ carry_in)
    );

    // Bit1 sum is XOR of inputs and carry from bit0.
    check_sum_bit1_xor: assert property (
        @(posedge clk) sum[1] == (num1[1] ^ num2[1] ^ maj3(num1[0], num2[0], carry_in))
    );

    // Bit2 sum is XOR of inputs and carry from bit1.
    check_sum_bit2_xor: assert property (
        @(posedge clk) sum[2] == (num1[2] ^ num2[2] ^ maj3(num1[1], num2[1], maj3(num1[0], num2[0], carry_in)))
    );

    // Bit3 sum is XOR of inputs and carry from bit2.
    check_sum_bit3_xor: assert property (
        @(posedge clk) sum[3] == (num1[3] ^ num2[3] ^ maj3(num1[2], num2[2], maj3(num1[1], num2[1], maj3(num1[0], num2[0], carry_in))))
    );

    // Final carry_out equals carry from bit3.
    check_carry_out_majority: assert property (
        @(posedge clk) carry_out == maj3(num1[3], num2[3], maj3(num1[2], num2[2], maj3(num1[1], num2[1], maj3(num1[0], num2[0], carry_in))))
    );

    // When no overflow occurs, carry_out must be 0.
    check_no_overflow_implies_carry0: assert property (
        @(posedge clk) ((num1 + num2 + carry_in) <= 5'd15) |-> (carry_out == 1'b0)
    );

    // When overflow occurs, carry_out must be 1.
    check_overflow_implies_carry1: assert property (
        @(posedge clk) ((num1 + num2 + carry_in) > 5'd15) |-> (carry_out == 1'b1)
    );

    // If num1==0 and carry_in==0, output equals num2 with no carry.
    check_passthrough_num2_when_num1_zero_cin0: assert property (
        @(posedge clk) ((num1 == 4'd0) && (carry_in == 1'b0)) |-> ((sum == num2) && (carry_out == 1'b0))
    );

    // If num2==0 and carry_in==0, output equals num1 with no carry.
    check_passthrough_num1_when_num2_zero_cin0: assert property (
        @(posedge clk) ((num2 == 4'd0) && (carry_in == 1'b0)) |-> ((sum == num1) && (carry_out == 1'b0))
    );

    // If num2==0 and carry_in==1, output equals num1+1 with carry on overflow.
    check_increment_when_cin1_num2_zero: assert property (
        @(posedge clk) ((num2 == 4'd0) && (carry_in == 1'b1)) |-> ((sum == (num1 + 5'd1)[3:0]) && (carry_out == (num1 == 4'hF)))
    );

    // Outputs remain stable when inputs do not change.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(num1) && $stable(num2) && $stable(carry_in)) |-> ($stable(sum) && $stable(carry_out))
    );
endmodule