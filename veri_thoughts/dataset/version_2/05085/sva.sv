module iddr_sva #
(
    parameter TARGET = "GENERIC",
    parameter IODDR_STYLE = "IODDR2",
    parameter WIDTH = 1
)
(
    input  logic             clk,
    input  logic [WIDTH-1:0] d,
    input  logic [WIDTH-1:0] q1,
    input  logic [WIDTH-1:0] q2
);

generate
if (TARGET == "XILINX") begin : xilinx_checks
end else if (TARGET == "ALTERA") begin : altera_checks
end else begin : generic_checks

    // q1 starts low because q_reg_1 is initialized to zero.
    check_q1_init_zero: assert property (
        @(posedge clk) $initstate |-> (q1 == {WIDTH{1'b0}})
    );

    // q2 starts low because q_reg_2 is initialized to zero.
    check_q2_init_zero: assert property (
        @(posedge clk) $initstate |-> (q2 == {WIDTH{1'b0}})
    );

    // q1 reflects the value of d sampled on the previous rising edge.
    check_q1_prev_posedge_sample: assert property (
        @(posedge clk) !$initstate |-> (q1 == $past(d))
    );

    // If d is unchanged across rising edges, q1 matches the current d value.
    check_q1_matches_current_d_when_d_stable: assert property (
        @(posedge clk) !$initstate |-> ((d != $past(d)) || (q1 == d))
    );

    // If d changes on a rising edge, q1 still holds the prior sampled value.
    check_q1_lags_current_d_on_toggle: assert property (
        @(posedge clk) !$initstate |-> ((d == $past(d)) || (q1 != d))
    );

end
endgenerate

endmodule