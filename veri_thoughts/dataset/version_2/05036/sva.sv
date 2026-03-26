module led_controller_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic [3:0]  out_port,
    input logic [31:0] readdata
);

    // Reset clears the LED output register.
    check_reset_clears_out_port: assert property (
        @(posedge clk) !reset_n |-> (out_port == 4'b0000)
    );

    // Reset clears the readback data.
    check_reset_clears_readdata: assert property (
        @(posedge clk) !reset_n |-> (readdata == 32'b0)
    );

    // Read data is always zero-extended.
    check_readdata_upper_bits_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (readdata[31:4] == 28'b0)
    );

    // Address 0 reads back the current output value.
    check_readback_at_address_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |-> (readdata == {28'b0, out_port})
    );

    // Nonzero addresses read back zero.
    check_readback_at_other_addresses: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |-> (readdata == 32'b0)
    );

    // A selected write to address 0 updates the output on the next cycle.
    check_write_updates_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(writedata[3:0]))
    );

    // Without a selected write to address 0, the output holds its value.
    check_out_port_holds_without_valid_write: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(out_port))
    );

endmodule