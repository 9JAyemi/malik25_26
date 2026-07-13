module memory_block_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic        out_port,
    input logic [31:0] readdata
);

    // Reset clears both visible storage outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) !reset_n |-> ((out_port == 1'b0) && (readdata == 32'h00000000))
    );

    // A valid write to address 0 updates the memory LSB seen on out_port.
    check_write_to_addr0_updates_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(writedata[0]))
    );

    // Without a valid write, the memory LSB seen on out_port holds its value.
    check_no_valid_write_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(out_port))
    );

    // A valid read from address 0 captures the current memory LSB into readdata bit 0.
    check_read_from_addr0_updates_readdata_lsb: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && write_n && (address == 2'b00)) |=> (readdata[0] == $past(out_port))
    );

    // Without a valid read, readdata holds its previous value.
    check_no_valid_read_holds_readdata: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(chipselect && write_n && (address == 2'b00)) |=> (readdata == $past(readdata))
    );

    // A write followed by a read on the next cycle returns the written 32-bit data.
    check_write_then_next_read_returns_written_data: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b00))
        ##1
        (chipselect && write_n && (address == 2'b00))
        |=> (readdata == $past(writedata, 2))
    );

endmodule