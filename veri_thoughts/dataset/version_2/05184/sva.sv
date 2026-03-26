module chacha_qr_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] c,
    input logic [31:0] d,
    input logic [31:0] a_prim,
    input logic [31:0] b_prim,
    input logic [31:0] c_prim,
    input logic [31:0] d_prim
);

    function automatic logic [31:0] rotl16(input logic [31:0] x);
        rotl16 = {x[15:0], x[31:16]};
    endfunction

    function automatic logic [31:0] rotl12(input logic [31:0] x);
        rotl12 = {x[19:0], x[31:20]};
    endfunction

    function automatic logic [31:0] rotl8(input logic [31:0] x);
        rotl8 = {x[23:0], x[31:24]};
    endfunction

    function automatic logic [31:0] rotl7(input logic [31:0] x);
        rotl7 = {x[24:0], x[31:25]};
    endfunction

    function automatic logic [31:0] d1_fn(
        input logic [31:0] a_in,
        input logic [31:0] b_in,
        input logic [31:0] d_in
    );
        logic [31:0] a0;
        a0   = a_in + b_in;
        d1_fn = rotl16(d_in ^ a0);
    endfunction

    function automatic logic [31:0] c0_fn(
        input logic [31:0] a_in,
        input logic [31:0] b_in,
        input logic [31:0] c_in,
        input logic [31:0] d_in
    );
        c0_fn = c_in + d1_fn(a_in, b_in, d_in);
    endfunction

    function automatic logic [31:0] b1_fn(
        input logic [31:0] a_in,
        input logic [31:0] b_in,
        input logic [31:0] c_in,
        input logic [31:0] d_in
    );
        b1_fn = rotl12(b_in ^ c0_fn(a_in, b_in, c_in, d_in));
    endfunction

    function automatic logic [31:0] a1_fn(
        input logic [31:0] a_in,
        input logic [31:0] b_in,
        input logic [31:0] c_in,
        input logic [31:0] d_in
    );
        logic [31:0] a0;
        a0   = a_in + b_in;
        a1_fn = a0 + b1_fn(a_in, b_in, c_in, d_in);
    endfunction

    function automatic logic [31:0] d3_fn(
        input logic [31:0] a_in,
        input logic [31:0] b_in,
        input logic [31:0] c_in,
        input logic [31:0] d_in
    );
        d3_fn = rotl8(d1_fn(a_in, b_in, d_in) ^ a1_fn(a_in, b_in, c_in, d_in));
    endfunction

    function automatic logic [31:0] c1_fn(
        input logic [31:0] a_in,
        input logic [31:0] b_in,
        input logic [31:0] c_in,
        input logic [31:0] d_in
    );
        c1_fn = c0_fn(a_in, b_in, c_in, d_in) + d3_fn(a_in, b_in, c_in, d_in);
    endfunction

    function automatic logic [31:0] b3_fn(
        input logic [31:0] a_in,
        input logic [31:0] b_in,
        input logic [31:0] c_in,
        input logic [31:0] d_in
    );
        b3_fn = rotl7(b1_fn(a_in, b_in, c_in, d_in) ^ c1_fn(a_in, b_in, c_in, d_in));
    endfunction

    // a_prim must match the quarterround a result.
    check_a_prim_matches_quarterround: assert property (
        @(posedge clk) a_prim == a1_fn(a, b, c, d)
    );

    // b_prim must match the quarterround b result.
    check_b_prim_matches_quarterround: assert property (
        @(posedge clk) b_prim == b3_fn(a, b, c, d)
    );

    // c_prim must match the quarterround c result.
    check_c_prim_matches_quarterround: assert property (
        @(posedge clk) c_prim == c1_fn(a, b, c, d)
    );

    // d_prim must match the quarterround d result.
    check_d_prim_matches_quarterround: assert property (
        @(posedge clk) d_prim == d3_fn(a, b, c, d)
    );

    // a_prim must be the first sum plus the rotated b path.
    check_a_prim_uses_first_sum_and_b1: assert property (
        @(posedge clk) a_prim == ((a + b) + b1_fn(a, b, c, d))
    );

    // d_prim must be the rotated xor of d1 and a_prim.
    check_d_prim_uses_d1_and_a_prim: assert property (
        @(posedge clk) d_prim == rotl8(d1_fn(a, b, d) ^ a_prim)
    );

    // c_prim must be c0 plus d_prim.
    check_c_prim_uses_c0_and_d_prim: assert property (
        @(posedge clk) c_prim == (c0_fn(a, b, c, d) + d_prim)
    );

    // b_prim must be the rotated xor of b1 and c_prim.
    check_b_prim_uses_b1_and_c_prim: assert property (
        @(posedge clk) b_prim == rotl7(b1_fn(a, b, c, d) ^ c_prim)
    );

    // Repeating the same inputs must repeat the same outputs.
    check_repeat_inputs_repeat_outputs: assert property (
        @(posedge clk)
        $past(1'b1) && ({a, b, c, d} == $past({a, b, c, d}))
        |-> ({a_prim, b_prim, c_prim, d_prim} == $past({a_prim, b_prim, c_prim, d_prim}))
    );

    // All-zero inputs must produce all-zero outputs.
    check_zero_inputs_produce_zero_outputs: assert property (
        @(posedge clk)
        ({a, b, c, d} == 128'h0) |-> ({a_prim, b_prim, c_prim, d_prim} == 128'h0)
    );

endmodule