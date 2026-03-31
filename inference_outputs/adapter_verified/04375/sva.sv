module reverse_last_two_bits_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);

// Next-cycle out equals previous in[1:0] concatenated with previous in[3:2].
    check_reverse_mapping: assert property (
        @(posedge clk) 1'b1 |=> (out == {$past(in[1:0]), $past(in[3:2])})
    );

// Upper out bit is previous in[1].
    check_out_msb_from_in1: assert property (
        @(posedge clk) 1'b1 |=> (out[1] == $past(in[1]))
    );

// Lower out bit is previous in[0].
    check_out_lsb_from_in0: assert property (
        @(posedge clk) 1'b1 |=> (out[0] == $past(in[0]))
    );

// Upper out bit equals previous in[3].
    check_out_msb_from_in3: assert property (
        @(posedge clk) 1'b1 |=> (out[1] == $past(in[3]))
    );

// Lower out bit equals previous in[2].
    check_out_lsb_from_in2: assert property (
        @(posedge clk) 1'b1 |=> (out[0] == $past(in[2]))
    );

endmodule
