module shift_register_assertions (
    input logic [3:0] in,
    input logic shift_dir,
    input logic clk,
    input logic [3:0] out
);

    property left_shift_function;
        logic [3:0] sampled_in;
        @(posedge clk)
            (1'b1, sampled_in = in) ##1 (shift_dir == 1'b0) |=> (out == (sampled_in << 1));
    endproperty

    property right_shift_function;
        logic [3:0] sampled_in;
        @(posedge clk)
            (1'b1, sampled_in = in) ##1 (shift_dir == 1'b1) |=> (out == (sampled_in >> 1));
    endproperty

    property left_shift_alignment;
        logic [3:0] sampled_in;
        @(posedge clk)
            (1'b1, sampled_in = in) ##1 (shift_dir == 1'b0) |=> (out[3:1] == sampled_in[2:0]);
    endproperty

    property right_shift_alignment;
        logic [3:0] sampled_in;
        @(posedge clk)
            (1'b1, sampled_in = in) ##1 (shift_dir == 1'b1) |=> (out[2:0] == sampled_in[3:1]);
    endproperty

    // When shift_dir is low, out is the prior cycle's input shifted left by one.
    check_left_shift_function: assert property (left_shift_function);

    // When shift_dir is high, out is the prior cycle's input shifted right by one.
    check_right_shift_function: assert property (right_shift_function);

    // A left shift preserves the lower three bits in out[3:1].
    check_left_shift_alignment: assert property (left_shift_alignment);

    // A right shift preserves the upper three bits in out[2:0].
    check_right_shift_alignment: assert property (right_shift_alignment);

    // A left shift always zero-fills the least significant output bit.
    check_left_shift_zero_fill: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (out[0] == 1'b0)
    );

    // A right shift always zero-fills the most significant output bit.
    check_right_shift_zero_fill: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (out[3] == 1'b0)
    );

endmodule