module data_transformer_assertions (
    input logic        clk,
    input logic [31:0] data_in,
    input logic [15:0] data_out
);

    // Output matches the RTL transform of the previous cycle input.
    check_output_transform_function: assert property (
        @(posedge clk)
        1'b1 |=> (
            data_out ==
            (($past(data_in[31:24]) == 8'hFF) ? 16'hFF00 :
             (($past(data_in[7:0]) == 8'h00) ? 16'h000F :
              {$past(data_in[31:24]), $past(data_in[7:0])}))
        )
    );

    // A top input byte of 0xFF forces FF00 on the next cycle.
    check_ff_prefix_transform: assert property (
        @(posedge clk)
        (data_in[31:24] == 8'hFF) |=> (data_out == 16'hFF00)
    );

    // A low input byte of 0x00 forces 000F when the 0xFF case is not active.
    check_zero_suffix_transform: assert property (
        @(posedge clk)
        (data_in[31:24] != 8'hFF && data_in[7:0] == 8'h00) |=> (data_out == 16'h000F)
    );

    // Without either special case, the selected input bytes pass through.
    check_passthrough_transform: assert property (
        @(posedge clk)
        (data_in[31:24] != 8'hFF && data_in[7:0] != 8'h00) |=> (
            data_out == {$past(data_in[31:24]), $past(data_in[7:0])}
        )
    );

    // When both conditions are true, the 0xFF check has priority.
    check_ff_priority_over_zero_suffix: assert property (
        @(posedge clk)
        (data_in[31:24] == 8'hFF && data_in[7:0] == 8'h00) |=> (data_out == 16'hFF00)
    );

endmodule