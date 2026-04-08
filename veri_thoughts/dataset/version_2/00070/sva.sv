module bidirectional_data_port_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] in,
    input logic dir,
    input logic [3:0] out,
    input logic [3:0] dout
);

    // Sampled low reset clears both outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) (reset == 1'b0) |-> (out == 4'b0000) && (dout == 4'b0000)
    );

    // With dir high, out loads the input value.
    check_out_loads_input_when_dir_high: assert property (
        @(posedge clk) disable iff (!reset) (dir == 1'b1) |=> (out == $past(in))
    );

    // With dir high, dout loads the reversed input value.
    check_dout_loads_reversed_input_when_dir_high: assert property (
        @(posedge clk) disable iff (!reset) (dir == 1'b1) |=> (dout == {$past(in[0]), $past(in[1]), $past(in[2]), $past(in[3])})
    );

    // With dir low, out still loads the input value.
    check_out_loads_input_when_dir_low: assert property (
        @(posedge clk) disable iff (!reset) (dir == 1'b0) |=> (out == $past(in))
    );

    // With dir low, dout holds its previous value.
    check_dout_holds_when_dir_low: assert property (
        @(posedge clk) disable iff (!reset) (dir == 1'b0) |=> (dout == $past(dout))
    );

endmodule