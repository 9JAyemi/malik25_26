module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    function automatic logic carry3(
        input logic x,
        input logic y,
        input logic z
    );
        carry3 = (x & y) | (x & z) | (y & z);
    endfunction

    function automatic logic c1_fn(
        input logic [3:0] x,
        input logic [3:0] y,
        input logic c
    );
        c1_fn = carry3(x[0], y[0], c);
    endfunction

    function automatic logic c2_fn(
        input logic [3:0] x,
        input logic [3:0] y,
        input logic c
    );
        c2_fn = carry3(x[1], y[1], c1_fn(x, y, c));
    endfunction

    function automatic logic c3_fn(
        input logic [3:0] x,
        input logic [3:0] y,
        input logic c
    );
        c3_fn = carry3(x[2], y[2], c2_fn(x, y, c));
    endfunction

    function automatic logic c4_fn(
        input logic [3:0] x,
        input logic [3:0] y,
        input logic c
    );
        c4_fn = carry3(x[3], y[3], c3_fn(x, y, c));
    endfunction

    function automatic logic [4:0] add5_fn(
        input logic [3:0] x,
        input logic [3:0] y,
        input logic c
    );
        add5_fn = {1'b0, x} + {1'b0, y} + c;
    endfunction

    // Combined output must equal the 4-bit addition with carry in.
    check_total_addition: assert property (
        @(posedge clk) disable iff (1'b0)
        {cout, sum} == add5_fn(a, b, cin)
    );

    // Bit 0 sum matches the first full-adder stage.
    check_sum_bit0: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit 1 sum uses the carry rippled from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[1] == (a[1] ^ b[1] ^ c1_fn(a, b, cin))
    );

    // Bit 2 sum uses the carry rippled from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[2] == (a[2] ^ b[2] ^ c2_fn(a, b, cin))
    );

    // Bit 3 sum uses the carry rippled from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[3] == (a[3] ^ b[3] ^ c3_fn(a, b, cin))
    );

    // Carry out matches the final ripple carry.
    check_carry_out: assert property (
        @(posedge clk) disable iff (1'b0)
        cout == c4_fn(a, b, cin)
    );

    // Carry out must be low when the total is below 16.
    check_no_overflow_range: assert property (
        @(posedge clk) disable iff (1'b0)
        (add5_fn(a, b, cin) < 5'd16) |-> !cout
    );

    // Carry out must be high when the total is 16 or more.
    check_overflow_range: assert property (
        @(posedge clk) disable iff (1'b0)
        (add5_fn(a, b, cin) >= 5'd16) |-> cout
    );

    // Adding zero with no carry-in passes a through unchanged.
    check_b_zero_passthrough: assert property (
        @(posedge clk) disable iff (1'b0)
        (b == 4'b0000 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // Adding zero with no carry-in passes b through unchanged.
    check_a_zero_passthrough: assert property (
        @(posedge clk) disable iff (1'b0)
        (a == 4'b0000 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

endmodule