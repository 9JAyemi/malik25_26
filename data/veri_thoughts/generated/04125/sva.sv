module bitwise_add_sub_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic select,
    input logic [7:0] out
);

    function automatic logic [7:0] bit_reverse(input logic [7:0] value);
        bit_reverse = {value[0], value[1], value[2], value[3], value[4], value[5], value[6], value[7]};
    endfunction

    // During reset, the output register stays cleared.
    check_reset_clears_out: assert property (
        @(posedge clk) !reset |-> (out == 8'h00)
    );

    property add_from_prior_inputs_p;
        logic [7:0] sampled_a;
        logic [7:0] sampled_b;
        @(posedge clk) disable iff (!reset)
            ((1'b1, sampled_a = in_a, sampled_b = in_b) ##1 (select == 1'b1))
            |-> ##1 (out == bit_reverse(sampled_a + sampled_b));
    endproperty
    // A high select uses the previous cycle's inputs and reaches out one cycle later.
    check_add_from_prior_inputs: assert property (add_from_prior_inputs_p);

    property sub_from_prior_inputs_p;
        logic [7:0] sampled_a;
        logic [7:0] sampled_b;
        @(posedge clk) disable iff (!reset)
            ((1'b1, sampled_a = in_a, sampled_b = in_b) ##1 (select == 1'b0))
            |-> ##1 (out == bit_reverse(sampled_a - sampled_b));
    endproperty
    // A low select uses the previous cycle's inputs and reaches out one cycle later.
    check_sub_from_prior_inputs: assert property (sub_from_prior_inputs_p);

    property first_active_cycle_zero_p;
        @(posedge clk) disable iff (!reset)
            $rose(reset) |-> (out == 8'h00);
    endproperty
    // The first sampled cycle after reset deassert still drives zero at out.
    check_first_active_cycle_zero: assert property (first_active_cycle_zero_p);

    property second_active_cycle_zero_p;
        @(posedge clk) disable iff (!reset)
            $rose(reset) |=> (out == 8'h00);
    endproperty
    // The second sampled cycle after reset deassert also drives zero at out.
    check_second_active_cycle_zero: assert property (second_active_cycle_zero_p);

endmodule