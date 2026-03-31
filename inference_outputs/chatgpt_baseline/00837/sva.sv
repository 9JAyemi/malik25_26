module wasca_hexdot_sva (
    input logic        clk,
    input logic        reset_n,
    input logic [1:0]  address,
    input logic        chipselect,
    input logic        write_n,
    input logic [31:0] writedata,
    input logic [5:0]  out_port,
    input logic [31:0] readdata
);
    ///// Reset behavior /////
    // While reset is asserted, drive out_port and readdata to 0.
    reset_clears_outputs: assert property (
        @(posedge clk) !reset_n |-> (out_port == 6'd0) && (readdata == 32'd0)
    );

    ///// Read datapath /////
    // Upper readdata bits are always zero.
    readdata_upper_zero_always: assert property (
        @(posedge clk) disable iff (!reset_n) readdata[31:6] == 26'd0
    );
    // When address == 0, readdata[5:0] reflects out_port.
    read_addr0_reflects_out_port: assert property (
        @(posedge clk) disable iff (!reset_n) (address == 2'd0) |-> (readdata[5:0] == out_port)
    );
    // When address != 0, entire readdata is zero.
    read_addr_nonzero_is_zero: assert property (
        @(posedge clk) disable iff (!reset_n) (address != 2'd0) |-> (readdata == 32'd0)
    );

    ///// Write/update behavior /////
    // Registered update rule: next out_port equals last-cycle writedata[5:0] on a write to address 0, else holds.
    out_port_update_rule: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |-> out_port ==
                ( ($past(chipselect) && !$past(write_n) && ($past(address) == 2'd0)) ? $past(writedata[5:0]) : $past(out_port) )
    );
    // If no write to address 0 in the current cycle, out_port holds its previous value.
    out_port_holds_without_write: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) && !(chipselect && !write_n && (address == 2'd0)) |-> (out_port == $past(out_port))
    );
    // A write with address != 0 does not change out_port.
    write_other_addr_no_effect: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) && chipselect && !write_n && (address != 2'd0) |-> (out_port == $past(out_port))
    );
    // A write to address 0 in the previous cycle updates out_port to that writedata[5:0].
    write_prev_cycle_updates_out: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n && chipselect && !write_n && (address == 2'd0)) |-> (out_port == $past(writedata[5:0]))
    );
    // With chipselect asserted and write_n HIGH at address 0, out_port must hold.
    hold_when_write_n_high_addr0: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) && chipselect && write_n && (address == 2'd0) |-> (out_port == $past(out_port))
    );
    // On reset release, if no same-cycle write to address 0, out_port remains 0.
    zero_after_reset_release_no_write: assert property (
        @(posedge clk) disable iff (!reset_n)
            $rose(reset_n) && !(chipselect && !write_n && (address == 2'd0)) |-> (out_port == 6'd0)
    );
endmodule