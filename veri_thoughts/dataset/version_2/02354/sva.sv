module data_modifier_sva (
    input logic clk,
    input logic [15:0] data_in,
    input logic [1:0] control,
    input logic [15:0] data_out
);
    // Next cycle output equals input when control==00.
    check_passthrough: assert property (
        @(posedge clk) (control == 2'b00) |=> (data_out == $past(data_in))
    );

    // Next cycle output equals bitwise NOT of input when control==01.
    check_invert: assert property (
        @(posedge clk) (control == 2'b01) |=> (data_out == ~$past(data_in))
    );

    // Next cycle output equals left shift by 1 with zero LSB when control==10.
    check_shift_left_value: assert property (
        @(posedge clk) (control == 2'b10) |=> (data_out == {$past(data_in)[14:0], 1'b0})
    );

    // Next cycle output equals right shift by 1 with zero MSB when control==11.
    check_shift_right_value: assert property (
        @(posedge clk) (control == 2'b11) |=> (data_out == {1'b0, $past(data_in)[15:1]})
    );

    // On left shift, next LSB is 0.
    check_shift_left_lsb_zero: assert property (
        @(posedge clk) (control == 2'b10) |=> (data_out[0] == 1'b0)
    );

    // On right shift, next MSB is 0.
    check_shift_right_msb_zero: assert property (
        @(posedge clk) (control == 2'b11) |=> (data_out[15] == 1'b0)
    );

    // On left shift, next upper bits track prior input [14:0].
    check_shift_left_bit_propagation: assert property (
        @(posedge clk) (control == 2'b10) |=> (data_out[15:1] == $past(data_in)[14:0])
    );

    // On right shift, next lower bits track prior input [15:1].
    check_shift_right_bit_propagation: assert property (
        @(posedge clk) (control == 2'b11) |=> (data_out[14:0] == $past(data_in)[15:1])
    );

    // One-cycle-late functional mapping matches the case statement for all control values.
    check_combined_map: assert property (
        @(posedge clk) 1'b1 |=> (
            data_out ==
                (($past(control) == 2'b00) ? $past(data_in) :
                 ($past(control) == 2'b01) ? ~$past(data_in) :
                 ($past(control) == 2'b10) ? {$past(data_in)[14:0], 1'b0} :
                                             {1'b0, $past(data_in)[15:1]})
        )
    );

    // On invert, next output XOR prior input is all ones.
    check_invert_xor_ones: assert property (
        @(posedge clk) (control == 2'b01) |=> ((data_out ^ $past(data_in)) == 16'hFFFF)
    );
endmodule