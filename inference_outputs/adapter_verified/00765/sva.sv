module mux_4to1_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic enable,
    input logic [3:0] out
);

// When enable is low, the output must be zero.
    check_disable_clears_out: assert property (
        @(posedge clk) !enable |-> (out == 4'b0000)
    );

// When enable is high and sel==00, out equals in0.
    check_sel00_when_enabled: assert property (
        @(posedge clk) enable && (sel == 2'b00) |-> (out == in0)
    );

// When enable is high and sel==01, out equals in1.
    check_sel01_when_enabled: assert property (
        @(posedge clk) enable && (sel == 2'b01) |-> (out == in1)
    );

// When enable is high and sel==10, out equals in2.
    check_sel10_when_enabled: assert property (
        @(posedge clk) enable && (sel == 2'b10) |-> (out == in2)
    );

// When enable is high and sel==11, out equals in3.
    check_sel11_when_enabled: assert property (
        @(posedge clk) enable && (sel == 2'b11) |-> (out == in3)
    );

endmodule
