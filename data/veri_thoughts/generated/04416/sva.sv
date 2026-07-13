module memory_module_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic [3:0]  out_port,
    input logic [31:0] readdata
);

    // Active-low reset clears both outputs.
    reset_clears_outputs: assert property (
        @(posedge clk) !reset_n |-> ((out_port == 4'h0) && (readdata == 32'h0))
    );

    // A selected write to address 0 loads the low nibble into out_port.
    write_addr0_updates_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(writedata[3:0]))
    );

    // With chipselect low, out_port holds its previous value.
    no_chipselect_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!chipselect) |=> (out_port == $past(out_port))
    );

    // When selected but not writing, out_port holds its previous value.
    write_high_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && write_n) |=> (out_port == $past(out_port))
    );

    // Writes to nonzero addresses do not change out_port.
    write_nonzero_addr_ignored: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address != 2'b00)) |=> (out_port == $past(out_port))
    );

    // Address 0 returns out_port in the low nibble.
    read_addr0_returns_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |-> (readdata == {28'h0, out_port})
    );

    // Nonzero addresses return zero on readdata.
    read_nonzero_addr_returns_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |-> (readdata == 32'h0)
    );

    // readdata upper bits are always zero.
    readdata_upper_bits_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (readdata[31:4] == 28'h0)
    );

endmodule