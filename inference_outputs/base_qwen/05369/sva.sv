module mux_adder_sva (
    input logic clk,
    input logic rst_n,
    input logic [2:0] sel_mux1,
    input logic [2:0] sel_mux2,
    input logic [3:0] data0_mux1,
    input logic [3:0] data1_mux1,
    input logic [3:0] data2_mux1,
    input logic [3:0] data3_mux1,
    input logic [3:0] data4_mux1,
    input logic [3:0] data5_mux1,
    input logic [3:0] data0_mux2,
    input logic [3:0] data1_mux2,
    input logic [3:0] data2_mux2,
    input logic [3:0] data3_mux2,
    input logic [3:0] data4_mux2,
    input logic [3:0] data5_mux2,
    input logic sel_mux,
    output logic [3:0] out
);
    // First multiplexer output should be one of the input data
    mux1_output: assert property (
        @(posedge clk) disable iff (!rst_n) mux1_out inside {[data0_mux1: data5_mux1]}
    );

    // Second multiplexer output should be one of the input data
    mux2_output: assert property (
        @(posedge clk) disable iff (!rst_n) mux2_out inside {[data0_mux2: data5_mux2]}
    );

    // Output of the adder should be the sum of the two multiplexer outputs
    adder_output: assert property (
        @(posedge clk) disable iff (!rst_n) out == mux1_out + mux2_out
    );

    // Control logic should select the correct multiplexer output
    control_logic: assert property (
        @(posedge clk) disable iff (!rst_n) (sel_mux == 1'b0) |-> out == mux1_out
    ) else $error("Control logic error: sel_mux = 0 but out is not equal to mux1_out");

    // At reset, all outputs should be zero
    reset_output: assert property (
        @(posedge clk) !rst_n |-> (out == 4'b0000)
    );
endmodule