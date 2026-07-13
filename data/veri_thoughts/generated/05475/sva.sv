module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] shift_amt,
    input logic dir,
    input logic [3:0] out
);

    // out matches the full case mapping.
    check_output_function: assert property (
        @(posedge clk)
        out == ((shift_amt == 2'b00) ? in :
                (shift_amt == 2'b01) ? ((dir == 1'b1) ? {in[2:0], in[3]} : {in[1:0], in[3:2]}) :
                (shift_amt == 2'b10) ? ((dir == 1'b1) ? {in[1:0], in[3:2]} : {in[2:0], in[3]}) :
                                      {in[0], in[3:1]})
    );

    // shift_amt 00 passes in directly to out.
    check_shift_amt_00_passthrough: assert property (
        @(posedge clk)
        (shift_amt == 2'b00) |-> (out == in)
    );

    // shift_amt 01 dir 1, or shift_amt 10 dir 0, selects {in[2:0],in[3]}.
    check_rotate_pattern_2301: assert property (
        @(posedge clk)
        (((shift_amt == 2'b01) && (dir == 1'b1)) ||
         ((shift_amt == 2'b10) && (dir == 1'b0)))
        |-> (out == {in[2:0], in[3]})
    );

    // shift_amt 01 dir 0, or shift_amt 10 dir 1, selects {in[1:0],in[3:2]}.
    check_rotate_pattern_0123: assert property (
        @(posedge clk)
        (((shift_amt == 2'b01) && (dir == 1'b0)) ||
         ((shift_amt == 2'b10) && (dir == 1'b1)))
        |-> (out == {in[1:0], in[3:2]})
    );

    // shift_amt 11 selects {in[0],in[3:1]} regardless of dir.
    check_shift_amt_11_mapping: assert property (
        @(posedge clk)
        (shift_amt == 2'b11) |-> (out == {in[0], in[3:1]})
    );

endmodule