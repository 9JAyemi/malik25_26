module full_adder_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c_in,
    input logic sum,
    input logic c_out,
    input logic p,
    input logic g
);
    // Sum and carry must equal the 2-bit addition of a, b, and c_in.
    check_add_result: assert property (
        @(posedge clk) {c_out, sum} == (a + b + c_in)
    );

    // p equals logical AND of a and b.
    check_p_and: assert property (
        @(posedge clk) p == (a & b)
    );

    // g equals logical XOR of a and b.
    check_g_xor: assert property (
        @(posedge clk) g == (a ^ b)
    );

    // sum equals XOR of a, b, and c_in.
    check_sum_triple_xor: assert property (
        @(posedge clk) sum == (a ^ b ^ c_in)
    );

    // c_out equals majority of a, b, and c_in.
    check_cout_majority: assert property (
        @(posedge clk) c_out == ((a & b) | (a & c_in) | (b & c_in))
    );

    // sum equals g XOR c_in.
    check_sum_g_xor_cin: assert property (
        @(posedge clk) sum == (g ^ c_in)
    );

    // c_out equals p OR (g AND c_in).
    check_cout_p_or_gcin: assert property (
        @(posedge clk) c_out == (p | (g & c_in))
    );

    // p and g cannot be HIGH at the same time.
    check_p_g_mutex: assert property (
        @(posedge clk) !(p & g)
    );

    // If p is HIGH (a&b=1), then sum equals c_in and c_out is 1.
    check_when_p_high: assert property (
        @(posedge clk) p |-> (sum == c_in) && (c_out == 1'b1)
    );

    // If g is HIGH (a^b=1), then sum is ~c_in and c_out equals c_in.
    check_when_g_high: assert property (
        @(posedge clk) g |-> (sum == ~c_in) && (c_out == c_in)
    );
endmodule