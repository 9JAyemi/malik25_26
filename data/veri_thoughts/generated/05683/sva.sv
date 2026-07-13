module retiming_blocks_sva #(
    parameter n = 8
)(
    input logic [n-1:0] in,
    input logic [n-1:0] out,
    input logic clk,
    input logic [n-1:0] reg_in,
    input logic [n-1:0] reg_out
);

    // reg_out mirrors reg_in combinationally.
    check_reg_out_mirrors_reg_in: assert property (
        @(posedge clk) reg_out == reg_in
    );

    // out is directly driven from reg_out.
    check_out_matches_reg_out: assert property (
        @(posedge clk) out == reg_out
    );

    // reg_in captures the input from the prior clock.
    check_reg_in_captures_prior_input: assert property (
        @(posedge clk) 1'b1 |=> (reg_in == $past(in))
    );

    // reg_out reflects the previously captured input.
    check_reg_out_reflects_prior_input: assert property (
        @(posedge clk) 1'b1 |=> (reg_out == $past(in))
    );

    // out is a one-cycle delayed version of in.
    check_out_is_one_cycle_delayed_input: assert property (
        @(posedge clk) 1'b1 |=> (out == $past(in))
    );

endmodule

bind retiming_blocks retiming_blocks_sva #(
    .n(n)
) retiming_blocks_sva_inst (
    .in(in),
    .out(out),
    .clk(clk),
    .reg_in(reg_in),
    .reg_out(reg_out)
);