module ssio_sdr_in_sva #(
    parameter TARGET = "GENERIC",
    parameter CLOCK_INPUT_STYLE = "BUFIO2",
    parameter WIDTH = 1
) (
    input logic             input_clk,
    input logic [WIDTH-1:0] input_d,
    input logic             output_clk,
    input logic [WIDTH-1:0] output_q
);

    // No RTL clock or reset; sample combinational behavior on input_clk.

    // output_clk is always the same as input_clk.
    check_output_clk_matches_input_clk: assert property (
        @(posedge input_clk) output_clk == input_clk
    );

    // output_q is always the same as input_d.
    check_output_q_matches_input_d: assert property (
        @(posedge input_clk) output_q == input_d
    );

    // output_q is the input_d value sampled on the previous input_clk edge.
    check_output_q_is_prev_input_d: assert property (
        @(posedge input_clk) 1'b1 |=> (output_q == $past(input_d))
    );

    // A rising input_d bit appears on output_q one input_clk later.
    check_output_q_rise_follows_input_d_rise: assert property (
        @(posedge input_clk) 1'b1 |=> ($rose(output_q[0]) |-> $rose(input_d[0]))
    );

    // A falling input_d bit appears on output_q one input_clk later.
    check_output_q_fall_follows_input_d_fall: assert property (
        @(posedge input_clk) 1'b1 |=> ($fell(output_q[0]) |-> $fell(input_d[0]))
    );

    // A change on input_d appears on output_q one input_clk later.
    check_output_q_change_follows_input_d_change: assert property (
        @(posedge input_clk) 1'b1 |=> ((output_q[0] != $past(output_q[0])) |-> (input_d[0] != $past(input_d[0])))
    );

    // A change on output_q implies a change on input_d one input_clk earlier.
    check_output_q_change_implies_input_d_change: assert property (
        @(posedge input_clk) 1'b1 |=> ((output_q[0] != $past(output_q[0])) |-> (input_d[0] != $past(input_d[0], 1)))
    );

    // A stable input_d keeps output_q stable one input_clk later.
    check_output_q_stable_when_input_d_stable: assert property (
        @(posedge input_clk) 1'b1 |=> ((input_d[0] == $past(input_d[0])) |-> (output_q[0] == $past(output_q[0])))
    );

endmodule