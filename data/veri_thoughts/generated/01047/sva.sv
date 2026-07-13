module mux4_to_1_enable_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic en,
    input logic [3:0] out,
    input logic [3:0] mux_out
);
    ///// Enable gating /////
    // When disabled, out is zero.
    check_out_zero_when_en_low: assert property (
        @(posedge clk) !en |-> (out == 4'b0000)
    );
    // When enabled, out equals mux_out.
    check_out_equals_mux_out_when_en: assert property (
        @(posedge clk) en |-> (out == mux_out)
    );

    ///// Internal mux select mapping /////
    // sel==00 routes in0 to mux_out.
    check_mux_sel00_routes_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (mux_out == in0)
    );
    // sel==01 routes in1 to mux_out.
    check_mux_sel01_routes_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (mux_out == in1)
    );
    // sel==10 routes in2 to mux_out.
    check_mux_sel10_routes_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (mux_out == in2)
    );
    // sel==11 routes in3 to mux_out.
    check_mux_sel11_routes_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (mux_out == in3)
    );

    ///// Output mapping with enable /////
    // When en and sel==00, out equals in0.
    check_out_matches_in0_when_en_sel00: assert property (
        @(posedge clk) (en && (sel == 2'b00)) |-> (out == in0)
    );
    // When en and sel==01, out equals in1.
    check_out_matches_in1_when_en_sel01: assert property (
        @(posedge clk) (en && (sel == 2'b01)) |-> (out == in1)
    );
    // When en and sel==10, out equals in2.
    check_out_matches_in2_when_en_sel10: assert property (
        @(posedge clk) (en && (sel == 2'b10)) |-> (out == in2)
    );
    // When en and sel==11, out equals in3.
    check_out_matches_in3_when_en_sel11: assert property (
        @(posedge clk) (en && (sel == 2'b11)) |-> (out == in3)
    );
endmodule