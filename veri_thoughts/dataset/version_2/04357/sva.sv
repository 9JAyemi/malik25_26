module spw_babasu_DATA_I_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic [8:0]  out_port,
    input logic [31:0] readdata
);

    // Active-low reset clears the stored output value.
    reset_clears_out_port: assert property (
        @(posedge clk) !reset_n |-> (out_port == 9'b0)
    );

    // Active-low reset forces read data low.
    reset_clears_readdata: assert property (
        @(posedge clk) !reset_n |-> (readdata == 32'b0)
    );

    // A write to address 0 updates out_port with writedata[8:0] on the next cycle.
    write_addr0_updates_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address == 2'b00)) |=> (out_port == $past(writedata[8:0]))
    );

    // Without a write to address 0, out_port holds its value.
    no_write_addr0_holds_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        !(chipselect && !write_n && (address == 2'b00)) |=> $stable(out_port)
    );

    // Address 0 reads back the stored value zero-extended to 32 bits.
    read_addr0_returns_out_port: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |-> (readdata == {23'b0, out_port})
    );

    // Nonzero addresses read as zero.
    read_other_addresses_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |-> (readdata == 32'b0)
    );

endmodule