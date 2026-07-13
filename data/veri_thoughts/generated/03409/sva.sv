module sync_ram_sva (
    input logic clk,
    input logic datain,
    input logic write_reset,
    input logic [2:0] waddr,
    input logic [2:0] raddr,
    input logic we,
    input logic dataout
);

    // Invalid read addresses drive zero.
    check_invalid_read_zero: assert property (
        @(posedge clk) disable iff (write_reset)
        ((raddr == 3'b110) || (raddr == 3'b111)) |-> (dataout == 1'b0)
    );

    // A reset seen on the prior cycle clears the visible read data.
    check_post_reset_output_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(write_reset) |-> (dataout == 1'b0)
    );

    // Without a write, a stable read address keeps the same data.
    check_hold_no_write_stable_read: assert property (
        @(posedge clk) disable iff (write_reset || $initstate)
        (!$past(write_reset) && ($past(we) !== 1'b1) && (raddr == $past(raddr)))
        |-> (dataout == $past(dataout))
    );

    // Writing a different address does not disturb the current read data.
    check_hold_write_other_addr: assert property (
        @(posedge clk) disable iff (write_reset || $initstate)
        (!$past(write_reset) && ($past(we) === 1'b1) && (raddr == $past(raddr)) &&
         ($past(waddr) != $past(raddr)))
        |-> (dataout == $past(dataout))
    );

    // A write to address 0 is visible when address 0 is read next cycle.
    check_write_addr0_readback: assert property (
        @(posedge clk) disable iff (write_reset || $initstate)
        (!$past(write_reset) && ($past(we) === 1'b1) &&
         ($past(waddr) == 3'b000) && (raddr == 3'b000))
        |-> (dataout == $past(datain))
    );

    // A write to address 1 is visible when address 1 is read next cycle.
    check_write_addr1_readback: assert property (
        @(posedge clk) disable iff (write_reset || $initstate)
        (!$past(write_reset) && ($past(we) === 1'b1) &&
         ($past(waddr) == 3'b001) && (raddr == 3'b001))
        |-> (dataout == $past(datain))
    );

    // A write to address 2 is visible when address 2 is read next cycle.
    check_write_addr2_readback: assert property (
        @(posedge clk) disable iff (write_reset || $initstate)
        (!$past(write_reset) && ($past(we) === 1'b1) &&
         ($past(waddr) == 3'b010) && (raddr == 3'b010))
        |-> (dataout == $past(datain))
    );

    // A write to address 3 is visible when address 3 is read next cycle.
    check_write_addr3_readback: assert property (
        @(posedge clk) disable iff (write_reset || $initstate)
        (!$past(write_reset) && ($past(we) === 1'b1) &&
         ($past(waddr) == 3'b011) && (raddr == 3'b011))
        |-> (dataout == $past(datain))
    );

    // A write to address 4 is visible when address 4 is read next cycle.
    check_write_addr4_readback: assert property (
        @(posedge clk) disable iff (write_reset || $initstate)
        (!$past(write_reset) && ($past(we) === 1'b1) &&
         ($past(waddr) == 3'b100) && (raddr == 3'b100))
        |-> (dataout == $past(datain))
    );

    // A write to address 5 is visible when address 5 is read next cycle.
    check_write_addr5_readback: assert property (
        @(posedge clk) disable iff (write_reset || $initstate)
        (!$past(write_reset) && ($past(we) === 1'b1) &&
         ($past(waddr) == 3'b101) && (raddr == 3'b101))
        |-> (dataout == $past(datain))
    );

endmodule