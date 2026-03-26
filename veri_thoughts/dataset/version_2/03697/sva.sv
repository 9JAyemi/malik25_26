module oh_oddr_assertions #(parameter DW = 1) (
    input logic           clk,
    input logic [DW-1:0]  din1,
    input logic [DW-1:0]  din2,
    input logic [DW-1:0]  out
);

    // A din1 sample on a rising edge must be observed on out at the following falling edge.
    check_din1_sample_reaches_next_negedge: assert property (
        @(posedge clk)
        1'b1 |=> @(negedge clk) (out == $past(din1, 1, 1'b1, @(posedge clk)))
    );

    // A din2 sample on a rising edge must be observed on out at the next rising edge.
    check_din2_sample_reaches_next_posedge: assert property (
        @(posedge clk)
        1'b1 |=> (out == $past(din2))
    );

endmodule