module shift_register_sva (
    input logic [3:0] in,
    input logic shift_dir,
    input logic clk,
    input logic [3:0] out
);

// Clock: clk (posedge). No reset in RTL. Logic: sequential with combinational output.

    // When shift_dir==1, out captures in on the next cycle.
    check_capture_when_shift1: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (out == $past(in))
    );

// When shift_dir==0, out captures in on the next cycle.
    check_capture_when_shift0: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (out == $past(in))
    );

// With shift_dir==1, out holds its value across consecutive cycles.
    check_hold_when_shift1: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (out == $past(out))
    );

// With shift_dir==0, out holds its value across consecutive cycles.
    check_hold_when_shift0: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (out == $past(out))
    );

// With shift_dir==1, out reflects the input from two cycles earlier.
    check_two_cycle_delay_when_shift1: assert property (
        @(posedge clk) (shift_dir == 1'b1) ##1 (shift_dir == 1'b1) |=> (out == $past(in,2))
    );

// With shift_dir==0, out reflects the input from two cycles earlier.
    check_two_cycle_delay_when_shift0: assert property (
        @(posedge clk) (shift_dir == 1'b0) ##1 (shift_dir == 1'b0) |=> (out == $past(in,2))
    );

endmodule
