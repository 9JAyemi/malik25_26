module barrel_shifter_sva (
    input logic [3:0] data_in,
    input logic [1:0] shift_amount,
    input logic [3:0] data_out
);
    // No clock/reset in DUT; combinational logic; sample on any input edge.

    // For shift_amount==00, output equals input.
    check_shift00_passthrough: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b00) |-> (data_out == data_in)
    );

    // For shift_amount==01, output is left rotate by 1.
    check_shift01_rotate1: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b01) |-> (data_out == {data_in[2:0], data_in[3]})
    );

    // For shift_amount==10, output is left rotate by 2.
    check_shift10_rotate2: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b10) |-> (data_out == {data_in[1:0], data_in[3:2]})
    );

    // For shift_amount==11, output is left rotate by 3.
    check_shift11_rotate3: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b11) |-> (data_out == {data_in[0], data_in[3:1]})
    );

    // For shift_amount==01, LSB comes from data_in[2].
    check_shift01_lsb_from_bit2: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b01) |-> (data_out[0] == data_in[2])
    );

    // For shift_amount==10, LSB comes from data_in[3].
    check_shift10_lsb_from_bit3: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b10) |-> (data_out[0] == data_in[3])
    );

    // For shift_amount==11, LSB comes from data_in[1].
    check_shift11_lsb_from_bit1: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b11) |-> (data_out[0] == data_in[1])
    );

    // For shift_amount==01, MSB comes from data_in[3].
    check_shift01_msb_from_bit3: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b01) |-> (data_out[3] == data_in[3])
    );

    // For shift_amount==10, MSB comes from data_in[0].
    check_shift10_msb_from_bit0: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b10) |-> (data_out[3] == data_in[0])
    );

    // For shift_amount==11, MSB comes from data_in[2].
    check_shift11_msb_from_bit2: assert property (
        @(posedge data_in[0] or negedge data_in[0] or
          posedge data_in[1] or negedge data_in[1] or
          posedge data_in[2] or negedge data_in[2] or
          posedge data_in[3] or negedge data_in[3] or
          posedge shift_amount[0] or negedge shift_amount[0] or
          posedge shift_amount[1] or negedge shift_amount[1])
        (shift_amount == 2'b11) |-> (data_out[3] == data_in[2])
    );

endmodule