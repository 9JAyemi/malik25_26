module adder_assertions (
    input logic        clk,
    input logic [7:0]  in0,
    input logic [7:0]  in1,
    input logic [15:0] out
);

    // A previous out of 16'hfffe forces the next registered out to zero.
    check_fffe_forces_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(out) === 16'hfffe) |-> (out === 16'h0000)
    );

    // Otherwise, the next low byte of out is the previous cycle's truncated input sum.
    check_registered_low_byte_sum: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(out) !== 16'hfffe) |-> ({1'b0, out[7:0]} === (({1'b0, $past(in0)} + {1'b0, $past(in1)}) & 9'h0ff))
    );

    // After the first clocked update, the upper byte of out is always zero.
    check_upper_byte_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        out[15:8] === 8'h00
    );

endmodule