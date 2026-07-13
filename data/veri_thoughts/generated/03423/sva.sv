module top_module_sva(
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [1:0]  select,
    input logic        clk,
    input logic [31:0] sum
);

    // Sum matches the full datapath implemented in the RTL.
    check_sum_matches_datapath: assert property (
        @(posedge clk)
        sum == ({(a[31:16] + b[31:16]), (a[15:0] + b[15:0])} + ((select == 2'b00) ? a : b))
    );

    // A zero select value makes the mux choose input a.
    check_select_zero_uses_a: assert property (
        @(posedge clk)
        (select == 2'b00) |-> (sum == ({(a[31:16] + b[31:16]), (a[15:0] + b[15:0])} + a))
    );

    // Any nonzero select value makes the mux choose input b.
    check_select_nonzero_uses_b: assert property (
        @(posedge clk)
        (select != 2'b00) |-> (sum == ({(a[31:16] + b[31:16]), (a[15:0] + b[15:0])} + b))
    );

    // Zero inputs on both data ports force a zero output.
    check_zero_inputs_yield_zero: assert property (
        @(posedge clk)
        ((a == 32'h00000000) && (b == 32'h00000000)) |-> (sum == 32'h00000000)
    );

    // With b zero and select zero, the output is a doubled modulo 32 bits.
    check_b_zero_and_select_zero_doubles_a: assert property (
        @(posedge clk)
        ((b == 32'h00000000) && (select == 2'b00)) |-> (sum == (a + a))
    );

    // With a zero and a nonzero select, the output is b doubled modulo 32 bits.
    check_a_zero_and_nonzero_select_doubles_b: assert property (
        @(posedge clk)
        ((a == 32'h00000000) && (select != 2'b00)) |-> (sum == (b + b))
    );

    // Stable inputs keep the combinational output stable.
    check_stable_inputs_keep_sum_stable: assert property (
        @(posedge clk)
        (!$initstate && $stable({a, b, select})) |-> $stable(sum)
    );

    // Different nonzero select encodings behave identically when a and b are unchanged.
    check_nonzero_select_values_equivalent: assert property (
        @(posedge clk)
        (!$initstate && $stable({a, b}) && ($past(select) != 2'b00) && (select != 2'b00)) |-> (sum == $past(sum))
    );

endmodule