module ssio_sdr_in_sva #(
    parameter WIDTH = 1
)(
    // DUT ports
    input  logic                  input_clk,
    input  logic [WIDTH-1:0]      input_d,
    input  logic                  output_clk,
    input  logic [WIDTH-1:0]      output_q,
    // Internal DUT signals used by SVA (present in RTL)
    input  logic                  clk_io,
    input  logic [WIDTH-1:0]      output_q_reg
);
    // Clocks: clk_io is the register clock; input_clk is the source; output_clk is derived. No reset in RTL.
    // Behavior: output_q is the registered copy of input_d captured on posedge clk_io.

    // Output port must reflect internal register.
    check_output_tied_to_reg: assert property (
        @(posedge clk_io) output_q == output_q_reg
    );

    // Registered 1-cycle delay from input_d to output_q.
    check_q_is_past_d: assert property (
        @(posedge clk_io) $past(1'b1) |-> (output_q == $past(input_d))
    );

    // Internal register captures input_d on the clock edge.
    check_reg_captures_d: assert property (
        @(posedge clk_io) $past(1'b1) |-> (output_q_reg == $past(input_d))
    );

    // If input_d is stable across the edge, output equals input now.
    check_stable_input_reflects_now: assert property (
        @(posedge clk_io) $past(1'b1) && $stable(input_d) |-> (output_q == input_d)
    );

    // If input_d changed this edge, output still shows the previous input value (no same-cycle comb path).
    check_no_comb_path_input_to_output: assert property (
        @(posedge clk_io) $past(1'b1) && !$stable(input_d) |-> (output_q != input_d)
    );

    // Any change in output_q implies a change in prior input_d.
    check_output_change_implies_prior_input_change: assert property (
        @(posedge clk_io) $past(1'b1,2) && (output_q != $past(output_q)) |-> ($past(input_d) != $past(input_d,2))
    );

    // If prior two input samples were equal, output does not change this edge.
    check_no_output_change_when_prior_inputs_equal: assert property (
        @(posedge clk_io) $past(1'b1,2) && ($past(input_d) == $past(input_d,2)) |-> (output_q == $past(output_q))
    );

    // Output delta equals prior input delta bitwise.
    check_bitwise_delta_propagation: assert property (
        @(posedge clk_io) $past(1'b1,2) |-> ((output_q ^ $past(output_q)) == ($past(input_d) ^ $past(input_d,2)))
    );

    // A single-bit toggle on input propagates as a single-bit toggle on output one cycle later.
    check_single_bit_toggle_propagation: assert property (
        @(posedge clk_io) $past(1'b1,2) && $onehot($past(input_d) ^ $past(input_d,2)) |-> $onehot(output_q ^ $past(output_q))
    );

    // Prior-cycle output reflects input from two cycles ago.
    check_prev_output_matches_two_cycle_old_input: assert property (
        @(posedge clk_io) $past(1'b1,2) |-> ($past(output_q) == $past(input_d,2))
    );
endmodule