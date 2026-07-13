module mux_4to1_enable_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic en,
    input logic [3:0] out
);

// When disabled, the output must be zero.
    check_disabled_forces_zero: assert property (
        @(posedge clk) !en |-> (out == 4'b0000)
    );

// When enabled and sel==00, out equals in0.
    check_sel00_when_enabled: assert property (
        @(posedge clk) en && (sel == 2'b00) |-> (out == in0)
    );

// When enabled and sel==01, out equals in1.
    check_sel01_when_enabled: assert property (
        @(posedge clk) en && (sel == 2'b01) |-> (out == in1)
    );

// When enabled and sel==10, out equals in2.
    check_sel10_when_enabled: assert property (
        @(posedge clk) en && (sel == 2'b10) |-> (out == in2)
    );

// When enabled and sel==11, out equals in3.
    check_sel11_when_enabled: assert property (
        @(posedge clk) en && (sel == 2'b11) |-> (out == in3)
    );

// When enabled, out must equal one of the four inputs.
    check_enabled_output_matches_inputs: assert property (
        @(posedge clk) en |-> (out == in0 || out == in1 || out == in2 || out == in3)
    );

// When enabled, out must equal one of the four inputs selected by sel.
    check_enabled_output_matches_selected_input: assert property (
        @(posedge clk) en |-> (out == (sel == 2'b00 ? in0 :
                                       sel == 2'b01 ? in1 :
                                       sel == 2'b10 ? in2 :
                                       sel == 2'b11 ? in3 :
                                       4'b0000))
    );

endmodule
