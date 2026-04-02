module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [35:0] in,
    output logic [31:0] out
);
    wire [3:0] seq_out;
    wire [31:0] change_out;
    wire [31:0] final_out;

    sequence_edge_detection seq_edge_detect (
        .clk(clk),
        .reset(reset),
        .in(in[3:0]),
        .out(seq_out)
    );

    change_detection change_detect (
        .clk(clk),
        .reset(reset),
        .in(in[35:4]),
        .out(change_out)
    );

    functional_module func_module (
        .seq_out(seq_out),
        .change_out(change_out),
        .final_out(final_out)
    );

    assign out = final_out;

    // Sequential logic assertions
    // Sequential edge detection logic
    seq_edge_detection_1: assert property (
        @(posedge clk) disable iff (!reset) (seq_out == in[3:0])
    ) else $error("Sequential edge detection logic failed");

    // Change detection logic
    change_detection_1: assert property (
        @(posedge clk) disable iff (!reset) (change_out == (in[35:4] & ~in[31:4]))
    ) else $error("Change detection logic failed");

    // Functional module logic
    functional_module_1: assert property (
        @(posedge clk) disable iff (!reset) (final_out == (seq_out | change_out))
    ) else $error("Functional module logic failed");

    // Combinational logic assertions
    // Sequential edge detection combinational logic
    seq_edge_detection_comb_1: assert property (
        @(posedge clk) disable iff (!reset) (seq_out == in[3:0])
    ) else $error("Sequential edge detection combinational logic failed");

    // Change detection combinational logic
    change_detection_comb_1: assert property (
        @(posedge clk) disable iff (!reset) (change_out == (in[35:4] & ~in[31:4]))
    ) else $error("Change detection combinational logic failed");

    // Functional module combinational logic
    functional_module_comb_1: assert property (
        @(posedge clk) disable iff (!reset) (final_out == (seq_out | change_out))
    ) else $error("Functional module combinational logic failed");
endmodule