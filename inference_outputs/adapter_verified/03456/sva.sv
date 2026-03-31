module shift_register_4bit_sva (
    input logic clk,
    input logic load,
    input logic [3:0] in,
    input logic [3:0] out,
    input logic ser_out
);

// Load captures in on the next cycle.
    check_load_captures_input: assert property (
        @(posedge clk) load |=> (out == $past(in))
    );

// When not loading, out rotates left by one bit.
    check_shift_left_when_not_loading: assert property (
        @(posedge clk) !load |=> (out == {$past(out[2:0]), $past(out[3])})
    );

// ser_out reflects the previous cycle's MSB.
    check_ser_out_follows_msb: assert property (
        @(posedge clk) 1'b1 |=> (ser_out == $past(out[3]))
    );

// A load followed by a shift returns the loaded value with the same MSB.
    check_load_then_shift_restores_msb: assert property (
        @(posedge clk) (load ##1 !load) |=> (out == $past(in) && ser_out == $past(in[3]))
    );

endmodule
