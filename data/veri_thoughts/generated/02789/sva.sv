module reverse_mux_and_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);
    // Out equals upper nibble AND selected 4-bit input
    check_function_equivalence: assert property (
        @(posedge clk) out == ((sel == 2'b00 ? in0 :
                                sel == 2'b01 ? in1 :
                                sel == 2'b10 ? in2 : in3) & in[7:4])
    );

    // When sel==00, out == (in0 & in[7:4])
    check_sel_00_map: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == (in0 & in[7:4]))
    );

    // When sel==01, out == (in1 & in[7:4])
    check_sel_01_map: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == (in1 & in[7:4]))
    );

    // When sel==10, out == (in2 & in[7:4])
    check_sel_10_map: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == (in2 & in[7:4]))
    );

    // When sel==11, out == (in3 & in[7:4])
    check_sel_11_map: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == (in3 & in[7:4]))
    );

    // out cannot have 1s where in[7:4] has 0s
    check_out_subset_of_upper_nibble: assert property (
        @(posedge clk) (out & ~in[7:4]) == 4'b0000
    );

    // If sel==00 and in0 is zero, out must be zero
    check_zero_when_sel00_in0_zero: assert property (
        @(posedge clk) ((sel == 2'b00) && (in0 == 4'b0000)) |-> (out == 4'b0000)
    );

    // If sel==01 and in1 is zero, out must be zero
    check_zero_when_sel01_in1_zero: assert property (
        @(posedge clk) ((sel == 2'b01) && (in1 == 4'b0000)) |-> (out == 4'b0000)
    );

    // If sel==10 and in2 is zero, out must be zero
    check_zero_when_sel10_in2_zero: assert property (
        @(posedge clk) ((sel == 2'b10) && (in2 == 4'b0000)) |-> (out == 4'b0000)
    );

    // If sel==11 and in3 is zero, out must be zero
    check_zero_when_sel11_in3_zero: assert property (
        @(posedge clk) ((sel == 2'b11) && (in3 == 4'b0000)) |-> (out == 4'b0000)
    );
endmodule