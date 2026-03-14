module barrel_shifter_4bit_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] shift,
    input logic [3:0] out
);
    ///// Functional mapping from previous-cycle inputs to registered output /////
    // If previous shift was 00, out equals previous in logically left-shifted by 1.
    map_shift00_full: assert property (
        @(posedge clk) ($past(shift) == 2'b00) |-> (out == ($past(in) << 1))
    );

    // If previous shift was 01, out equals previous in logically right-shifted by 1.
    map_shift01_full: assert property (
        @(posedge clk) ($past(shift) == 2'b01) |-> (out == ($past(in) >> 1))
    );

    // If previous shift was 10, out equals previous in rotated left by 2.
    map_shift10_full: assert property (
        @(posedge clk) ($past(shift) == 2'b10) |-> (out == { $past(in[1:0]), $past(in[3:2]) })
    );

    ///// Bit-level consequences of each transform /////
    // For shift 00, LSB of out is 0 (inserted zero on left shift).
    shift00_lsb_zero: assert property (
        @(posedge clk) ($past(shift) == 2'b00) |-> (out[0] == 1'b0)
    );

    // For shift 00, upper bits of out come from previous lower bits of in.
    shift00_upper_from_lower: assert property (
        @(posedge clk) ($past(shift) == 2'b00) |-> (out[3:1] == $past(in[2:0]))
    );

    // For shift 01, MSB of out is 0 (inserted zero on right shift).
    shift01_msb_zero: assert property (
        @(posedge clk) ($past(shift) == 2'b01) |-> (out[3] == 1'b0)
    );

    // For shift 01, lower bits of out come from previous upper bits of in.
    shift01_lower_from_upper: assert property (
        @(posedge clk) ($past(shift) == 2'b01) |-> (out[2:0] == $past(in[3:1]))
    );

    // For shift 10, out[3:2] equal previous in[1:0].
    shift10_upper_matches_prev_lsb: assert property (
        @(posedge clk) ($past(shift) == 2'b10) |-> (out[3:2] == $past(in[1:0]))
    );

    // For shift 10, out[1:0] equal previous in[3:2].
    shift10_lower_matches_prev_msb: assert property (
        @(posedge clk) ($past(shift) == 2'b10) |-> (out[1:0] == $past(in[3:2]))
    );

    ///// Stability rule /////
    // If in and shift are unchanged over two cycles, out remains unchanged.
    stable_out_if_inputs_stable: assert property (
        @(posedge clk) ($past(in,2) == $past(in)) && ($past(shift,2) == $past(shift)) |-> (out == $past(out))
    );
endmodule