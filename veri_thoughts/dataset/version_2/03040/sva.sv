module pio_egmenable_sva (
    input logic [1:0] address,
    input logic       chipselect,
    input logic       clk,
    input logic       reset_n,
    input logic       write_n,
    input logic       writedata,
    input logic       out_port,
    input logic       readdata
);

    // Reset clears the stored output and therefore the readback value.
    check_reset_clears_outputs: assert property (
        @(posedge clk) !reset_n |-> (out_port == 1'b0) && (readdata == 1'b0)
    );

    // Address 0 reads back the stored output bit.
    check_read_addr0_returns_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |-> (readdata == out_port)
    );

    // Any nonzero address reads back zero.
    check_read_nonzero_addr_returns_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |-> (readdata == 1'b0)
    );

    // A selected write to address 0 updates the output on the next clock.
    check_write_addr0_updates_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(writedata))
    );

    // Without a selected write to address 0, the output register holds its value.
    check_no_target_write_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(out_port))
    );

    // Writes to nonzero addresses do not modify the output register.
    check_nonzero_address_write_is_ignored: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address != 2'b00)) |=> (out_port == $past(out_port))
    );

endmodule