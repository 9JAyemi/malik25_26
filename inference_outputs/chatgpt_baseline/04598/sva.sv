module adder4_assertions (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    function automatic logic fa_sum(input logic x, input logic y, input logic c);
        fa_sum = x ^ y ^ c;
    endfunction

    function automatic logic fa_cout(input logic x, input logic y, input logic c);
        fa_cout = (x & y) | (x & c) | (y & c);
    endfunction

    // The 5-bit result matches unsigned addition of a, b, and cin.
    check_total_addition: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Sum bit 0 matches the first full-adder stage.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == fa_sum(a[0], b[0], cin)
    );

    // Sum bit 1 matches the ripple carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == fa_sum(a[1], b[1], fa_cout(a[0], b[0], cin))
    );

    // Sum bit 2 matches the ripple carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == fa_sum(a[2], b[2], fa_cout(a[1], b[1], fa_cout(a[0], b[0], cin)))
    );

    // Sum bit 3 matches the ripple carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == fa_sum(a[3], b[3], fa_cout(a[2], b[2], fa_cout(a[1], b[1], fa_cout(a[0], b[0], cin))))
    );

    // Carry out matches the final ripple-carry stage.
    check_cout_chain: assert property (
        @(posedge clk) cout == fa_cout(a[3], b[3], fa_cout(a[2], b[2], fa_cout(a[1], b[1], fa_cout(a[0], b[0], cin))))
    );

    // Adding zero with cin low passes a through unchanged.
    check_passthrough_a: assert property (
        @(posedge clk) (b == 4'h0 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // Adding zero with cin low passes b through unchanged.
    check_passthrough_b: assert property (
        @(posedge clk) (a == 4'h0 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

    // Zero plus zero produces cin in the LSB with no carry out.
    check_zero_plus_cin: assert property (
        @(posedge clk) (a == 4'h0 && b == 4'h0) |-> (sum == {3'b000, cin} && cout == 1'b0)
    );

endmodule