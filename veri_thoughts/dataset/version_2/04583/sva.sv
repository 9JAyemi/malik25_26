module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    function automatic logic majority3 (
        input logic x,
        input logic y,
        input logic z
    );
        majority3 = (x & y) | (x & z) | (y & z);
    endfunction

    // Combined sum and carry match 4-bit addition with carry in.
    check_total_result: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, A} + {1'b0, B} + cin)
    );

    // Sum bit 0 follows the full-adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (A[0] ^ B[0] ^ cin)
    );

    // Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == (A[1] ^ B[1] ^ majority3(A[0], B[0], cin))
    );

    // Sum bit 2 uses the carry generated from bits 0 and 1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == (A[2] ^ B[2] ^ majority3(A[1], B[1], majority3(A[0], B[0], cin)))
    );

    // Sum bit 3 uses the carry generated from bits 0 through 2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == (A[3] ^ B[3] ^ majority3(A[2], B[2], majority3(A[1], B[1], majority3(A[0], B[0], cin))))
    );

    // Final carry out follows the ripple-carry chain.
    check_carry_out: assert property (
        @(posedge clk) cout == majority3(A[3], B[3], majority3(A[2], B[2], majority3(A[1], B[1], majority3(A[0], B[0], cin))))
    );

endmodule