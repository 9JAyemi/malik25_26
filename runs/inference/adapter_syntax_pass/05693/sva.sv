module shift_register_sva (
    input logic clk,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // Load captures data_in into data_out on the next clock.
    check_load_captures_input: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

    // Without load, data_out rotates left by one bit.
    check_shift_rotates_output: assert property (
        @(posedge clk) !load |=> (data_out == { $past(data_out[2:0]), $past(data_out[3]) })
    );

    // The least-significant bit comes from the previous MSB when shifting.
    check_shift_wraps_msb_to_lsb: assert property (
        @(posedge clk) !load |=> (data_out[0] == $past(data_out[3]))
    );

    // A zero input is captured when load is asserted.
    check_load_captures_zero_input: assert property (
        @(posedge clk) (load && (data_in == 4'h0)) |=> (data_out == 4'h0)
    );

    // A zero output remains zero on the next clock when shifting.
    check_shift_keeps_zero_output: assert property (
        @(posedge clk) (!load && (data_out == 4'h0)) |=> (data_out == 4'h0)
    );

endmodule