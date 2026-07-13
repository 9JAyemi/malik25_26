module abs_val_sva (
    input logic [3:0] num_in,
    input logic       clk,
    input logic       rst,
    input logic [3:0] abs_val_out
);

    // clk is the sampling clock; rst is active-high in the DUT.
    // The DUT has combinational datapath logic feeding a registered output.

    logic [3:0] neg_num;
    logic       is_neg;
    logic [3:0] mux_out;
    logic [3:0] pos_num;

    assign neg_num = ~num_in + 4'b0001;
    assign is_neg  = (num_in[3] == 1'b1);
    assign mux_out = is_neg ? neg_num : num_in;
    assign pos_num = {1'b0, mux_out[2:0]} + 4'b0001;

    // A sampled reset forces the next sampled output to zero.
    check_reset_cycle_clears_next_sample: assert property (
        @(posedge clk) rst |=> (abs_val_out == 4'b0000)
    );

    // The registered output can only be 0 through 8 on the next sample.
    check_next_output_stays_in_0_to_8_range: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (abs_val_out <= 4'b1000)
    );

    // Next sample is either the prior computed pos_num or reset zero.
    check_next_output_is_loaded_pos_num_or_reset_zero: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> ((abs_val_out == $past(pos_num)) || (abs_val_out == 4'b0000))
    );

    // A non-negative input loads its zero-extended low 3 bits plus 1, unless reset drives zero.
    check_non_negative_input_loads_incremented_value_or_zero: assert property (
        @(posedge clk) disable iff (rst)
        !is_neg |=> ((abs_val_out == ({1'b0, $past(num_in[2:0])} + 4'b0001)) || (abs_val_out == 4'b0000))
    );

    // A negative input loads the low 3 bits of its two's complement plus 1, unless reset drives zero.
    check_negative_input_loads_negated_low_bits_plus_one_or_zero: assert property (
        @(posedge clk) disable iff (rst)
        is_neg |=> ((abs_val_out == ({1'b0, $past(neg_num[2:0])} + 4'b0001)) || (abs_val_out == 4'b0000))
    );

    // Input 0 loads 1 on the next sample, unless reset drives zero.
    check_zero_input_maps_to_one_or_zero: assert property (
        @(posedge clk) disable iff (rst)
        (num_in == 4'b0000) |=> ((abs_val_out == 4'b0001) || (abs_val_out == 4'b0000))
    );

    // Input 7 loads 8 on the next sample, unless reset drives zero.
    check_seven_input_maps_to_eight_or_zero: assert property (
        @(posedge clk) disable iff (rst)
        (num_in == 4'b0111) |=> ((abs_val_out == 4'b1000) || (abs_val_out == 4'b0000))
    );

    // Input 8 loads 1 on the next sample, unless reset drives zero.
    check_most_negative_input_maps_to_one_or_zero: assert property (
        @(posedge clk) disable iff (rst)
        (num_in == 4'b1000) |=> ((abs_val_out == 4'b0001) || (abs_val_out == 4'b0000))
    );

    // Input 15 loads 2 on the next sample, unless reset drives zero.
    check_minus_one_input_maps_to_two_or_zero: assert property (
        @(posedge clk) disable iff (rst)
        (num_in == 4'b1111) |=> ((abs_val_out == 4'b0010) || (abs_val_out == 4'b0000))
    );

    // Input 9 loads 8 on the next sample, unless reset drives zero.
    check_minus_seven_input_maps_to_eight_or_zero: assert property (
        @(posedge clk) disable iff (rst)
        (num_in == 4'b1001) |=> ((abs_val_out == 4'b1000) || (abs_val_out == 4'b0000))
    );

endmodule