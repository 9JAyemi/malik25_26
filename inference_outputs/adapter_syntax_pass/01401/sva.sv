module shift_register_sva (
    input logic       clk,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // Load captures data_in into the register on the next cycle.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

    // When not loading, the register shifts left and inserts 0 in bit 0.
    check_shift_behavior: assert property (
        @(posedge clk) !load |=> (data_out == {$past(data_out[2:0]), 1'b0})
    );

    // Bit 3 always reflects the previous bit 2 when shifting.
    check_shift_bit3_mapping: assert property (
        @(posedge clk) !load |=> (data_out[3] == $past(data_out[2]))
    );

    // Bit 2 always reflects the previous bit 1 when shifting.
    check_shift_bit2_mapping: assert property (
        @(posedge clk) !load |=> (data_out[2] == $past(data_out[1]))
    );

    // Bit 1 always reflects the previous bit 0 when shifting.
    check_shift_bit1_mapping: assert property (
        @(posedge clk) !load |=> (data_out[1] == $past(data_out[0]))
    );

    // Bit 0 is cleared whenever the register is not loading.
    check_shift_bit0_zero: assert property (
        @(posedge clk) !load |=> (data_out[0] == 1'b0)
    );

endmodule