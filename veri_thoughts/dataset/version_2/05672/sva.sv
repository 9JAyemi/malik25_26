module and_gate_delayed_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic y
);

    property output_matches_delayed_and_p;
        logic sampled_and;
        @(posedge clk) (1'b1, sampled_and = (a & b)) |=> ##2 (y == sampled_and);
    endproperty

    // y matches the sampled a&b value after the two pipeline stages.
    check_output_matches_delayed_and: assert property (output_matches_delayed_and_p);

    // A sampled high AND must propagate to y after the pipeline delay.
    check_high_and_reaches_output: assert property (
        @(posedge clk) (a & b) |=> ##2 y
    );

    // A sampled low on a must force y low after the pipeline delay.
    check_a_low_reaches_output_low: assert property (
        @(posedge clk) (!a) |=> ##2 !y
    );

    // A sampled low on b must force y low after the pipeline delay.
    check_b_low_reaches_output_low: assert property (
        @(posedge clk) (!b) |=> ##2 !y
    );

endmodule