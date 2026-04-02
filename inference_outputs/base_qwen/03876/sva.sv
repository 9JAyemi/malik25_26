module mux4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    output logic [3:0] out
);
    // Sequential logic is not present, so we use combinational assertions.

    // Mux output should match the selected input
    mux_output: assert property (
        @(posedge clk) disable iff (!rst_n) (out == (sel == 2'b00 ? in0 : (sel == 2'b01 ? in1 : (sel == 2'b10 ? in2 : in3))))
    ) else $error("Mux output does not match selected input");

    // Mux select signal should be within valid range
    mux_select_range: assert property (
        @(posedge clk) disable iff (!rst_n) (sel inside {[0:3]})
    ) else $error("Mux select signal out of range");

endmodule