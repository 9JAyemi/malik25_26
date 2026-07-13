module ripple_carry_adder_sva(
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic cin,
    input logic [7:0] sum,
    input logic cout
);

    function automatic logic carry_into(
        input integer idx,
        input logic [7:0] a,
        input logic [7:0] b,
        input logic c
    );
        logic carry;
        integer j;
        begin
            carry = c;
            for (j = 0; j < idx; j = j + 1) begin
                carry = (a[j] & b[j]) | (a[j] & carry) | (b[j] & carry);
            end
            carry_into = carry;
        end
    endfunction

    // Full 9-bit result matches unsigned addition.
    check_total_sum: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, A} + {1'b0, B} + {{8{1'b0}}, cin})
    );

    // Sum bit 0 uses the external carry-in.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (A[0] ^ B[0] ^ carry_into(0, A, B, cin))
    );

    // Sum bit 1 uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == (A[1] ^ B[1] ^ carry_into(1, A, B, cin))
    );

    // Sum bit 2 uses the carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == (A[2] ^ B[2] ^ carry_into(2, A, B, cin))
    );

    // Sum bit 3 uses the carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == (A[3] ^ B[3] ^ carry_into(3, A, B, cin))
    );

    // Sum bit 4 uses the carry from bit 3.
    check_sum_bit4: assert property (
        @(posedge clk) sum[4] == (A[4] ^ B[4] ^ carry_into(4, A, B, cin))
    );

    // Sum bit 5 uses the carry from bit 4.
    check_sum_bit5: assert property (
        @(posedge clk) sum[5] == (A[5] ^ B[5] ^ carry_into(5, A, B, cin))
    );

    // Sum bit 6 uses the carry from bit 5.
    check_sum_bit6: assert property (
        @(posedge clk) sum[6] == (A[6] ^ B[6] ^ carry_into(6, A, B, cin))
    );

    // Sum bit 7 uses the carry from bit 6.
    check_sum_bit7: assert property (
        @(posedge clk) sum[7] == (A[7] ^ B[7] ^ carry_into(7, A, B, cin))
    );

    // Carry out is the carry after bit 7.
    check_carry_out: assert property (
        @(posedge clk) cout == carry_into(8, A, B, cin)
    );

endmodule