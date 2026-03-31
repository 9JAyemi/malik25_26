module Span12Mux_s5_v_assertions (
    input logic clk,
    input logic [11:0] I,
    input logic O
);

// O is 1 only when I equals 12'b000000000001.
    check_o_one_when_i_one: assert property (
        @(posedge clk) (O == 1'b1) |-> (I == 12'b000000000001)
    );

// O is 0 only when I equals 12'b000000000010.
    check_o_zero_when_i_two: assert property (
        @(posedge clk) (O == 1'b0) |-> (I == 12'b000000000010)
    );

// I equals 12'b000000000001 implies O is 1.
    check_one_implies_o_one: assert property (
        @(posedge clk) (I == 12'b000000000001) |-> (O == 1'b1)
    );

// I equals 12'b000000000010 implies O is 0.
    check_two_implies_o_zero: assert property (
        @(posedge clk) (I == 12'b000000000010) |-> (O == 1'b0)
    );

// O is 1 only for the single input value 12'b000000000001.
    check_o_one_only_for_one: assert property (
        @(posedge clk) (O == 1'b1) |-> (I == 12'b000000000001)
    );

// O is 0 only for the single input value 12'b000000000010.
    check_o_zero_only_for_two: assert property (
        @(posedge clk) (O == 1'b0) |-> (I == 12'b000000000010)
    );

// For all other 12-bit input values, O must be 0.
    check_o_zero_for_other_inputs: assert property (
        @(posedge clk) (I != 12'b000000000001) && (I != 12'b000000000010) |-> (O == 1'b0)
    );

// For all other 12-bit input values, O must be 1.
    check_o_one_for_other_inputs: assert property (
        @(posedge clk) (I != 12'b000000000001) && (I != 12'b000000000010) |-> (O == 1'b1)
    );

endmodule
