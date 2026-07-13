module priority_encoder_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);

// in[3] has highest priority and drives out to 00.
    check_in3_priority: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 4'b1110) |-> (out == 2'b00)
    );

// in[2] has priority when in[3] is low and drives out to 01.
    check_in2_priority: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in == 4'b1101) || (in == 4'b0111)) |-> (out == 2'b01)
    );

// in[1] has priority when in[2:3] are low and drives out to 10.
    check_in1_priority: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in == 4'b1011) || (in == 4'b0011)) |-> (out == 2'b10)
    );

// in[0] has priority when in[1:2] are low and drives out to 11.
    check_in0_priority: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in == 4'b0111) || (in == 4'b0001)) |-> (out == 2'b11)
    );

// Default case with no asserted inputs drives out to 00.
    check_default_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 4'b0000) |-> (out == 2'b00)
    );

// Any asserted input other than in[3] drives out to 01.
    check_any_one_drives_01: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in[2] == 1'b1) || (in[1] == 1'b1) || (in[0] == 1'b1)) |-> (out == 2'b01)
    );

// Any asserted input other than in[2] drives out to 10.
    check_any_two_drives_10: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in[3] == 1'b0) && ((in[1] == 1'b1) || (in[0] == 1'b1))) |-> (out == 2'b10)
    );

// Any asserted input other than in[1] drives out to 11.
    check_any_three_drives_11: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in[3] == 1'b0) && (in[2] == 1'b0) && (in[0] == 1'b1)) |-> (out == 2'b11)
    );

endmodule
