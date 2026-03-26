module pipeline_stage_2_sva (
    input logic [3:0] in,
    input logic [3:0] out,
    input logic clk
);

    // Out is the input value captured on the previous clock.
    check_out_is_registered_input: assert property (
        @(posedge clk) 1'b1 |=> (out == $past(in))
    );

    // If input is unchanged across clocks, output matches that value on the next clock.
    check_out_matches_held_input: assert property (
        @(posedge clk) 1'b1 |=> (($past(in) != in) || (out == in))
    );

    // If input changes across clocks, output still shows the earlier sampled value.
    check_out_lags_input_change: assert property (
        @(posedge clk) 1'b1 |=> (($past(in) == in) || (out != in))
    );

endmodule