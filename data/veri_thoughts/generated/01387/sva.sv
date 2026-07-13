module nios_system_sram_addr_sva (
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        clk,
    input logic        reset_n,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic [10:0] out_port,
    input logic [31:0] readdata
);
    // During reset, out_port must be 0.
    reset_out_port_zero: assert property (
        @(posedge clk) !reset_n |-> (out_port == 11'b0)
    );

    // During reset, readdata must be 0.
    reset_readdata_zero: assert property (
        @(posedge clk) !reset_n |-> (readdata[31:11] == 21'b0 && readdata[10:0] == 11'b0)
    );

    // Upper 21 bits of readdata are always zero.
    readdata_upper_zero_always: assert property (
        @(posedge clk) disable iff (!reset_n) (readdata[31:11] == 21'b0)
    );

    // When address == 0, readdata[10:0] equals out_port.
    readdata_low_matches_out_port_on_addr0: assert property (
        @(posedge clk) disable iff (!reset_n) (address == 2'b00) |-> (readdata[10:0] == out_port)
    );

    // When address != 0, readdata[10:0] is zero.
    readdata_low_zero_on_addr_non0: assert property (
        @(posedge clk) disable iff (!reset_n) (address != 2'b00) |-> (readdata[10:0] == 11'b0)
    );

    // A write to address 0 updates out_port on the next cycle to writedata[10:0].
    write_updates_out_port: assert property (
        @(posedge clk) disable iff (!reset_n) (chipselect && ~write_n && (address == 2'b00)) |=> (out_port == $past(writedata[10:0]))
    );

    // A write to a nonzero address does not change out_port.
    write_other_addr_does_not_change_out_port: assert property (
        @(posedge clk) disable iff (!reset_n) $past(reset_n) && (chipselect && ~write_n && (address != 2'b00)) |=> (out_port == $past(out_port))
    );

    // If no write to address 0 occurs, out_port holds its value.
    out_port_holds_without_write_hit0: assert property (
        @(posedge clk) disable iff (!reset_n) $past(reset_n) && !(chipselect && ~write_n && (address == 2'b00)) |=> (out_port == $past(out_port))
    );

    // Any change to out_port must be caused by a prior write to address 0.
    out_port_change_requires_prev_write_hit0: assert property (
        @(posedge clk) disable iff (!reset_n) $past(reset_n) && (out_port != $past(out_port)) |-> $past(chipselect && ~write_n && (address == 2'b00))
    );

    // After a write to address 0, if address is 0 next cycle, readdata returns the written value.
    read_after_write_returns_written_value: assert property (
        @(posedge clk) disable iff (!reset_n) (chipselect && ~write_n && (address == 2'b00)) |=> ((address == 2'b00) ? (readdata[10:0] == $past(writedata[10:0])) : 1'b1)
    );
endmodule