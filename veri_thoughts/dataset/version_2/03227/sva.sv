module my_module_sva #(
    parameter WIDTH = 64
) (
    input logic clk,
    input logic [WIDTH-1:0] data_in,
    input logic [WIDTH-1:0] data_out,
    input logic [12:0] in0,
    input logic [12:0] in1,
    input logic [12:0] in2,
    input logic [12:0] in3,
    input logic [12:0] in4,
    input logic [12:0] in5,
    input logic [12:0] in6,
    input logic [12:0] in7,
    input logic [12:0] in8,
    input logic [12:0] in9,
    input logic [12:0] in10,
    input logic [12:0] in11,
    input logic [12:0] in12,
    input logic [WIDTH-1:0] probe0,
    input logic [WIDTH-1:0] probe1,
    input logic [12:0] inv_in
);

    // data_out is directly driven from probe1.
    check_data_out_mirrors_probe1: assert property (
        @(posedge clk) data_out == probe1
    );

    // probe0 holds the data_in value sampled on the previous posedge.
    check_probe0_captures_prev_data_in: assert property (
        @(posedge clk) 1'b1 |=> (probe0 == $past(data_in))
    );

    // inv_in holds the inverted prior posedge value of in0 after truncation.
    check_inv_in_captures_prev_inverted_in0: assert property (
        @(posedge clk) 1'b1 |=> (inv_in == ~$past(in0))
    );

    // probe1 holds the probe0 value sampled on the previous negedge.
    check_probe1_captures_prev_probe0: assert property (
        @(negedge clk) 1'b1 |=> (probe1 == $past(probe0))
    );

    // probe1 reflects the data_in value from the previous posedge.
    check_probe1_reflects_prev_data_in: assert property (
        @(posedge clk) 1'b1 |=> (probe1 == $past(data_in))
    );

    // data_out reflects the data_in value from the previous posedge.
    check_data_out_reflects_prev_data_in: assert property (
        @(posedge clk) 1'b1 |=> (data_out == $past(data_in))
    );

endmodule