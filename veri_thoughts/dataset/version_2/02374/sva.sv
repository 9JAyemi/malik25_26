module right_barrel_shifter_sva (
    input logic CLK,
    input logic [7:0] d_in,
    input logic [2:0] shift_amount,
    input logic [7:0] d_out
);
    // d_out must equal input when shift_amount == 0.
    check_shift0_identity: assert property (
        @(posedge CLK) (shift_amount == 3'd0) |=> (d_out == d_in)
    );

    // d_out must be a right rotate by 1 when shift_amount == 1.
    check_shift1_rotate: assert property (
        @(posedge CLK) (shift_amount == 3'd1) |=> (d_out == {d_in[0], d_in[7:1]})
    );

    // d_out must be a right rotate by 2 when shift_amount == 2.
    check_shift2_rotate: assert property (
        @(posedge CLK) (shift_amount == 3'd2) |=> (d_out == {d_in[1:0], d_in[7:2]})
    );

    // d_out must be a right rotate by 3 when shift_amount == 3.
    check_shift3_rotate: assert property (
        @(posedge CLK) (shift_amount == 3'd3) |=> (d_out == {d_in[2:0], d_in[7:3]})
    );

    // d_out must be a right rotate by 4 when shift_amount == 4.
    check_shift4_rotate: assert property (
        @(posedge CLK) (shift_amount == 3'd4) |=> (d_out == {d_in[3:0], d_in[7:4]})
    );

    // d_out must be a right rotate by 5 when shift_amount == 5.
    check_shift5_rotate: assert property (
        @(posedge CLK) (shift_amount == 3'd5) |=> (d_out == {d_in[4:0], d_in[7:5]})
    );

    // d_out must be a right rotate by 6 when shift_amount == 6.
    check_shift6_rotate: assert property (
        @(posedge CLK) (shift_amount == 3'd6) |=> (d_out == {d_in[5:0], d_in[7:6]})
    );

    // d_out must be zero when shift_amount == 7.
    check_shift7_zero: assert property (
        @(posedge CLK) (shift_amount == 3'd7) |=> (d_out == 8'h00)
    );

    // d_out must always match the full case mapping of the RTL.
    check_full_mapping: assert property (
        @(posedge CLK)
            1'b1 |=> (
                d_out == (
                    (shift_amount == 3'd0) ? d_in :
                    (shift_amount == 3'd1) ? {d_in[0],     d_in[7:1]} :
                    (shift_amount == 3'd2) ? {d_in[1:0],   d_in[7:2]} :
                    (shift_amount == 3'd3) ? {d_in[2:0],   d_in[7:3]} :
                    (shift_amount == 3'd4) ? {d_in[3:0],   d_in[7:4]} :
                    (shift_amount == 3'd5) ? {d_in[4:0],   d_in[7:5]} :
                    (shift_amount == 3'd6) ? {d_in[5:0],   d_in[7:6]} :
                                              8'h00
                )
            )
    );
endmodule