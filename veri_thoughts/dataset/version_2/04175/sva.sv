module data_pass_module_sva(
    input logic clk,
    input logic [23:0] data_in,
    input logic [23:0] data_out
);

    // data_out captures the previous cycle's data_in value.
    check_data_capture: assert property (
        @(posedge clk) 1'b1 |=> (data_out == $past(data_in))
    );

    // A sampled change on data_in appears on data_out one cycle later.
    check_input_change_propagates: assert property (
        @(posedge clk) $changed(data_in) |=> $changed(data_out)
    );

    // Sampled stability on data_in leads to stability on data_out one cycle later.
    check_input_stability_propagates: assert property (
        @(posedge clk) $stable(data_in) |=> $stable(data_out)
    );

endmodule