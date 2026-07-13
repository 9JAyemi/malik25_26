module adder_4bit_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] s,
    input logic cout
);

    // RTL is combinational with no native clock or reset; clk is a sampling clock.
    function automatic logic [4:0] expected_sum(
        input logic [3:0] aa,
        input logic [3:0] bb,
        input logic cc
    );
        begin
            expected_sum = {1'b0, aa} + {1'b0, bb} + {4'b0, cc};
        end
    endfunction

    function automatic logic [3:0] expected_s(
        input logic [3:0] aa,
        input logic [3:0] bb,
        input logic cc
    );
        logic [4:0] tmp;
        begin
            tmp = {1'b0, aa} + {1'b0, bb} + {4'b0, cc};
            expected_s = tmp[3:0];
        end
    endfunction

    function automatic logic expected_cout(
        input logic [3:0] aa,
        input logic [3:0] bb,
        input logic cc
    );
        logic [4:0] tmp;
        begin
            tmp = {1'b0, aa} + {1'b0, bb} + {4'b0, cc};
            expected_cout = tmp[4];
        end
    endfunction

    // Combined outputs match the 5-bit addition result.
    check_full_sum_match: assert property (
        @(posedge clk) {cout, s} == expected_sum(a, b, cin)
    );

    // s matches the lower 4 bits of the addition result.
    check_sum_low_bits: assert property (
        @(posedge clk) s == expected_s(a, b, cin)
    );

    // cout matches the carry bit of the addition result.
    check_carry_out: assert property (
        @(posedge clk) cout == expected_cout(a, b, cin)
    );

    // The sum LSB is the xor of the input LSBs and carry-in.
    check_lsb_xor: assert property (
        @(posedge clk) s[0] == (a[0] ^ b[0] ^ cin)
    );

    // Stable inputs imply stable outputs.
    check_stable_io: assert property (
        @(posedge clk) $stable({a, b, cin}) |-> $stable({cout, s})
    );

    // Zero inputs produce zero sum and zero carry.
    check_zero_case: assert property (
        @(posedge clk) (a == 4'h0 && b == 4'h0 && cin == 1'b0) |-> ({cout, s} == 5'h00)
    );

    // 4'hF + 4'h1 wraps the sum and raises carry-out.
    check_wrap_carry_case: assert property (
        @(posedge clk) (a == 4'hF && b == 4'h1 && cin == 1'b0) |-> ({cout, s} == 5'h10)
    );

    // 4'hF + 4'hF + 1 produces the maximum 5-bit result.
    check_max_case: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> ({cout, s} == 5'h1F)
    );

endmodule