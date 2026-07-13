module shift_left_sva (
    input logic        clk,
    input logic [15:0] data_in,
    input logic        shift_control,
    input logic [15:0] data_out
);

    // data_out follows the prior cycle's selected assignment.
    check_registered_update: assert property (
        @(posedge clk)
        1'b1 |=> data_out == ($past(shift_control) ? {$past(data_in[14:0]), 1'b0} : $past(data_in))
    );

    // In shift mode, the next upper bits come from the prior lower bits.
    check_shift_upper_bits: assert property (
        @(posedge clk)
        shift_control |=> data_out[15:1] == $past(data_in[14:0])
    );

    // In shift mode, the next least significant bit is zero.
    check_shift_lsb_zero: assert property (
        @(posedge clk)
        shift_control |=> data_out[0] == 1'b0
    );

    // In pass-through mode, the next output equals the prior input.
    check_passthrough_update: assert property (
        @(posedge clk)
        !shift_control |=> data_out == $past(data_in)
    );

endmodule