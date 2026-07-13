module barrel_shifter_sva (
    input logic [3:0] data_in,
    input logic [1:0] shift,
    input logic       clk,
    input logic [3:0] data_out
);

    function automatic logic [3:0] shift_value (
        input logic [3:0] d,
        input logic [1:0] s
    );
        begin
            case (s)
                2'b00: shift_value = d;
                2'b01: shift_value = {d[2:0], 1'b0};
                2'b10: shift_value = {1'b0, d[3:1]};
                2'b11: shift_value = {2'b00, d[3:2]};
                default: shift_value = 4'bxxxx;
            endcase
        end
    endfunction

    // data_out is the previous cycle's shifted version of data_in.
    check_output_matches_previous_shift: assert property (
        @(posedge clk)
        (!$initstate && !$isunknown($past({data_in, shift}))) |-> (data_out == shift_value($past(data_in), $past(shift)))
    );

    // shift 00 passes the previous input through unchanged.
    check_shift_00_pass_through: assert property (
        @(posedge clk)
        (!$initstate && !$isunknown($past({data_in, shift})) && ($past(shift) == 2'b00)) |-> (data_out == $past(data_in))
    );

    // shift 01 left shifts the previous input by one with zero fill.
    check_shift_01_left_shift_one: assert property (
        @(posedge clk)
        (!$initstate && !$isunknown($past({data_in, shift})) && ($past(shift) == 2'b01)) |-> (data_out == {$past(data_in[2:0]), 1'b0})
    );

    // shift 10 right shifts the previous input by one with zero fill.
    check_shift_10_right_shift_one: assert property (
        @(posedge clk)
        (!$initstate && !$isunknown($past({data_in, shift})) && ($past(shift) == 2'b10)) |-> (data_out == {1'b0, $past(data_in[3:1])})
    );

    // shift 11 right shifts the previous input by two with zero fill.
    check_shift_11_right_shift_two: assert property (
        @(posedge clk)
        (!$initstate && !$isunknown($past({data_in, shift})) && ($past(shift) == 2'b11)) |-> (data_out == {2'b00, $past(data_in[3:2])})
    );

endmodule