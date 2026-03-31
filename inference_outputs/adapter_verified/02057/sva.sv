module shift_register_sva (
    input logic clk,
    input logic in,
    input logic shift,
    input logic out,
    input logic [7:0] register
);

// Register captures the previous input value on the shift edge.
    check_register_captures_input: assert property (
        @(posedge clk) shift |=> (register[7:1] == $past(register[6:0])) && (register[0] == $past(in))
    );

// Output reflects the MSB of the register on the shift edge.
    check_out_follows_register_msb: assert property (
        @(posedge clk) shift |=> (out == $past(register[7]))
    );

// Output is the previous input value on the shift edge.
    check_out_follows_input: assert property (
        @(posedge clk) shift |=> (out == $past(in))
    );

// A high input drives the register MSB high on the next shift edge.
    check_input_high_sets_msb: assert property (
        @(posedge clk) (in == 1'b1) |=> (register[7] == 1'b1)
    );

// A low input drives the register MSB low on the next shift edge.
    check_input_low_clears_msb: assert property (
        @(posedge clk) (in == 1'b0) |=> (register[7] == 1'b0)
    );

endmodule
